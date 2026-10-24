-- Prove2me | solution 1 for StrictCompatLB.RegularDegree.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:31:41.365875+00:00
-- url     : https://prove2.me/submissions/bf6d0211-95e1-478a-b539-d352ef7d1da3

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular

open Finset Filter MeasureTheory Topology

namespace StrictCompatLB.RegularDegree.RDInfra

open StrictCompatLB.MeanField StrictCompatLB.RegularDegree

/-- Rows (server neighbourhoods) of weight exactly `k`. -/
def rowSet (m k : ℕ) : Finset (Fin m → Bool) :=
  Finset.univ.filter (fun r => (Finset.univ.filter (fun w => r w = true)).card = k)

lemma card_rowSet (m k : ℕ) : (rowSet m k).card = m.choose k := by
  classical
  have : (rowSet m k).card = ((Finset.univ : Finset (Fin m)).powersetCard k).card := by
    apply Finset.card_nbij' (fun r => Finset.univ.filter (fun w => r w = true))
      (fun S => fun w => decide (w ∈ S))
    · intro r hr
      simp only [rowSet, Finset.coe_filter, Finset.mem_univ, true_and] at hr
      simpa [Finset.mem_powersetCard] using hr
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
      simp [rowSet, hS.2]
    · intro r _
      funext w; simp
    · intro S _
      ext w; simp
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma card_rowSet_mem (m k : ℕ) (hk : 1 ≤ k) (w : Fin m) :
    ((rowSet m k).filter (fun r => r w = true)).card = (m - 1).choose (k - 1) := by
  classical
  have : ((rowSet m k).filter (fun r => r w = true)).card
      = (((Finset.univ : Finset (Fin m)).powersetCard k).filter (fun S => {w} ⊆ S)).card := by
    apply Finset.card_nbij' (fun r => Finset.univ.filter (fun w => r w = true))
      (fun S => fun w => decide (w ∈ S))
    · intro r hr
      simp only [rowSet, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simpa [Finset.mem_powersetCard] using hr
    · intro S hS
      simp only [Finset.coe_filter, Finset.mem_powersetCard, Set.mem_setOf_eq] at hS
      simp only [rowSet, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq, decide_eq_true_eq]
      refine ⟨by simpa using hS.1.2, by simpa using hS.2⟩
    · intro r _
      funext w; simp
    · intro S _
      ext w; simp
  rw [this, Finset.card_filter_powersetCard_subset {w} _ k (by simp) (by simpa using hk)]
  simp

open Classical in
lemma reg_eq_piFinset (N m k : ℕ) :
    (Finset.univ.filter (fun a : Fin N → Fin m → Bool => IsServerRegular k a))
      = Fintype.piFinset (fun _ => rowSet m k) := by
  ext a
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  simp [IsServerRegular, rowSet]

open Classical in
/-- The law of the random graph, as counting. -/
lemma prob_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M c : ℕ → ℕ)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (N : ℕ) (E : Finset (Fin N → Fin (M N) → Bool)) :
    P (adj N ⁻¹' (E : Set (Fin N → Fin (M N) → Bool)))
      = ((E.filter (fun a => IsServerRegular (c N) a)).card : ENNReal)
        * (((Nat.choose (M N) (c N) : ℕ) : ENNReal) ^ N)⁻¹ := by
  classical
  have hU : adj N ⁻¹' (E : Set (Fin N → Fin (M N) → Bool)) = ⋃ a ∈ E, adj N ⁻¹' {a} := by
    ext ω; simp
  rw [hU, measure_biUnion_finset]
  · simp_rw [(hadj N).2]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  · intro a _ b _ hab
    exact Disjoint.preimage _ (Set.disjoint_singleton.mpr hab)
  · intro a _
    exact (hadj N).1 (measurableSet_singleton a)

/-- Borel–Cantelli in the form used below. -/
lemma ae_eventually_of_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → Set Ω) (b : ℕ → ℝ) (hb : Summable b) (N₀ : ℕ)
    (hs : ∀ N ≥ N₀, P (s N) ≤ ENNReal.ofReal (b N)) :
    ∀ᵐ ω ∂P, ∀ᶠ N in atTop, ω ∉ s N := by
  classical
  let s' : ℕ → Set Ω := fun N => if N₀ ≤ N then s N else ∅
  have hs' : (∑' i, P (s' i)) ≠ ⊤ := by
    have hle : ∀ i, P (s' i) ≤ ENNReal.ofReal (if N₀ ≤ i then |b i| else 0) := by
      intro i
      simp only [s']
      split_ifs with h
      · exact (hs i h).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
      · simp
    have hsum : Summable (fun i => if N₀ ≤ i then |b i| else 0) := by
      apply Summable.of_norm_bounded hb.abs
      intro i
      split_ifs <;> simp
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · exact ENNReal.ofReal_ne_top
    · intro i; split_ifs with h
      · exact abs_nonneg _
      · exact le_rfl
    · exact hsum
  filter_upwards [ae_eventually_notMem hs'] with ω hω
  filter_upwards [hω, eventually_ge_atTop N₀] with N h1 h2
  simpa [s', h2] using h1

/-- Column count. -/
def col {N m : ℕ} (a : Fin N → Fin m → Bool) (w : Fin m) : ℕ :=
  (Finset.univ.filter (fun u => a u w = true)).card

lemma pow_col {N m : ℕ} (a : Fin N → Fin m → Bool) (w : Fin m) (y : ℝ) :
    y ^ col a w = ∏ u, (if a u w = true then y else 1) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, col]

lemma row_sum_y (m k : ℕ) (w : Fin m) (y : ℝ) :
    ∑ r ∈ rowSet m k, (if r w = true then y else 0)
      = y * (((rowSet m k).filter (fun r => r w = true)).card : ℝ) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma row_sum_y1 (m k : ℕ) (w : Fin m) (y : ℝ) :
    ∑ r ∈ rowSet m k, (if r w = true then y else 1)
      = y * (((rowSet m k).filter (fun r => r w = true)).card : ℝ)
        + (((rowSet m k).card : ℝ) - (((rowSet m k).filter (fun r => r w = true)).card : ℝ)) := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one,
    mul_comm]
  congr 1
  have := Finset.card_filter_add_card_filter_not (s := rowSet m k) (fun r => r w = true)
  have h2 : (((rowSet m k).filter (fun r => r w = true)).card : ℝ)
      + (((rowSet m k).filter (fun r => ¬ r w = true)).card : ℝ) = ((rowSet m k).card : ℝ) := by
    exact_mod_cast this
  linarith

/-- The key product identity: `Σ_{a regular} 𝟙{a v w} y^{col_w(a)}`. -/
lemma sum_reg_col (N m k : ℕ) (v : Fin N) (w : Fin m) (y : ℝ) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin N => rowSet m k),
        (if a v w = true then y ^ col a w else 0)
      = (y * (((rowSet m k).filter (fun r => r w = true)).card : ℝ)) *
        (y * (((rowSet m k).filter (fun r => r w = true)).card : ℝ)
          + (((rowSet m k).card : ℝ) - (((rowSet m k).filter (fun r => r w = true)).card : ℝ)))
          ^ (N - 1) := by
  classical
  let g : Fin N → (Fin m → Bool) → ℝ := fun u r =>
    if u = v then (if r w = true then y else 0) else (if r w = true then y else 1)
  have hprod : ∀ a : Fin N → Fin m → Bool,
      (if a v w = true then y ^ col a w else 0) = ∏ u, g u (a u) := by
    intro a
    by_cases hv : a v w = true
    · rw [if_pos hv, pow_col]
      apply Finset.prod_congr rfl
      intro u _
      by_cases hu : u = v
      · subst hu; simp [g, hv]
      · simp [g, hu]
    · rw [if_neg hv]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [g, hv]
  simp_rw [hprod]
  rw [← Finset.prod_univ_sum]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
  congr 1
  · simp only [g, if_pos rfl]
    exact row_sum_y m k w y
  · have : ∀ u ∈ Finset.univ.erase v, ∑ r ∈ rowSet m k, g u r
        = ∑ r ∈ rowSet m k, (if r w = true then y else 1) := by
      intro u hu
      have hu' : u ≠ v := Finset.ne_of_mem_erase hu
      simp [g, hu']
    rw [Finset.prod_congr rfl this, Finset.prod_const, row_sum_y1]
    congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]

lemma exp_le_quad {x : ℝ} (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + 3 / 4 * x ^ 2 := by
  have h := Real.exp_bound hx (n := 2) (by norm_num)
  have e : ∑ i ∈ Finset.range 2, x ^ i / (i.factorial : ℝ) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [e] at h
  have h2 : |x| ^ 2 = x ^ 2 := sq_abs x
  rw [h2] at h
  have : Real.exp x - (1 + x) ≤ x ^ 2 * ((Nat.succ 2 : ℝ) / ((Nat.factorial 2 : ℝ) * 2)) :=
    (le_abs_self _).trans h
  norm_num [Nat.factorial] at this
  linarith

/-- Low-degree neighbour count of server `v`. -/
noncomputable def lowNbr {N m : ℕ} (a : Fin N → Fin m → Bool) (t : ℝ) (v : Fin N) : ℕ :=
  (Finset.univ.filter (fun w => a v w = true ∧ (col a w : ℝ) ≤ t)).card

lemma card_filter_exists_le {α ι : Type*} [Fintype ι] (S : Finset α) (Q : ι → α → Prop)
    [∀ i, DecidablePred (Q i)] [DecidablePred (fun a => ∃ i, Q i a)] :
    (S.filter (fun a => ∃ i, Q i a)).card ≤ ∑ i, (S.filter (Q i)).card := by
  classical
  have : S.filter (fun a => ∃ i, Q i a) = Finset.univ.biUnion (fun i => S.filter (Q i)) := by
    ext a; simp
  rw [this]
  exact Finset.card_biUnion_le

lemma markov_count {α : Type*} (S : Finset α) (f : α → ℝ) (hf : ∀ a ∈ S, 0 ≤ f a) (s : ℝ)
    [DecidablePred (fun a => s < f a)] :
    ((S.filter (fun a => s < f a)).card : ℝ) * s ≤ ∑ a ∈ S, f a := by
  calc ((S.filter (fun a => s < f a)).card : ℝ) * s
      = ∑ a ∈ S.filter (fun a => s < f a), s := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ S.filter (fun a => s < f a), f a := by
        apply Finset.sum_le_sum; intro a ha; exact (Finset.mem_filter.mp ha).2.le
    _ ≤ ∑ a ∈ S, f a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a ha _ => hf a ha)

lemma lowNbr_le {N m : ℕ} (a : Fin N → Fin m → Bool) (t lam : ℝ) (hlam : 0 ≤ lam) (v : Fin N) :
    (lowNbr a t v : ℝ) ≤ ∑ w, (if a v w = true then
      Real.exp (lam * t) * Real.exp (-lam) ^ col a w else 0) := by
  classical
  rw [lowNbr, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro w _
  by_cases h1 : a v w = true
  · rw [if_pos h1]
    by_cases h2 : (col a w : ℝ) ≤ t
    · rw [if_pos ⟨h1, h2⟩]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      apply Real.one_le_exp
      nlinarith
    · rw [if_neg (fun h => h2 h.2)]; push_cast; positivity
  · rw [if_neg (fun h => h1 h.1), if_neg h1]; simp

/-- Counting core of Lemma A.5. -/
lemma count_bad_A5 (N m k : ℕ) (hk : 1 ≤ k) (s t lam : ℝ) (hs : 0 < s) (hlam : 0 ≤ lam) :
    (((Fintype.piFinset (fun _ : Fin N => rowSet m k)).filter
        (fun a => ∃ v, s < (lowNbr a t v : ℝ))).card : ℝ)
      ≤ N / s * (Real.exp (lam * t) * (m *
        ((Real.exp (-lam) * ((m - 1).choose (k - 1) : ℝ)) *
        (Real.exp (-lam) * ((m - 1).choose (k - 1) : ℝ)
          + ((m.choose k : ℝ) - ((m - 1).choose (k - 1) : ℝ))) ^ (N - 1)))) := by
  classical
  set S := Fintype.piFinset (fun _ : Fin N => rowSet m k)
  set y := Real.exp (-lam)
  set Q : ℝ := (y * ((m - 1).choose (k - 1) : ℝ)) *
        (y * ((m - 1).choose (k - 1) : ℝ) + ((m.choose k : ℝ) - ((m - 1).choose (k - 1) : ℝ)))
          ^ (N - 1)
  have hcol : ∀ v : Fin N, ∀ w : Fin m,
      ∑ a ∈ S, (if a v w = true then y ^ col a w else 0) = Q := by
    intro v w
    rw [sum_reg_col, card_rowSet_mem m k hk w, card_rowSet]
  have hv : ∀ v : Fin N, ((S.filter (fun a => s < (lowNbr a t v : ℝ))).card : ℝ)
      ≤ (1 / s) * (Real.exp (lam * t) * (m * Q)) := by
    intro v
    have h1 := markov_count S (fun a => (lowNbr a t v : ℝ)) (fun a _ => by positivity) s
    have h2 : ∑ a ∈ S, (lowNbr a t v : ℝ) ≤ Real.exp (lam * t) * (m * Q) := by
      calc ∑ a ∈ S, (lowNbr a t v : ℝ)
          ≤ ∑ a ∈ S, ∑ w, (if a v w = true then
              Real.exp (lam * t) * y ^ col a w else 0) :=
            Finset.sum_le_sum (fun a _ => lowNbr_le a t lam hlam v)
        _ = ∑ w, Real.exp (lam * t) * ∑ a ∈ S, (if a v w = true then y ^ col a w else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro w _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> simp
        _ = Real.exp (lam * t) * (m * Q) := by
            simp_rw [hcol]
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs]
    linarith
  calc (((S.filter (fun a => ∃ v, s < (lowNbr a t v : ℝ))).card : ℝ))
      ≤ ∑ v : Fin N, ((S.filter (fun a => s < (lowNbr a t v : ℝ))).card : ℝ) := by
        exact_mod_cast card_filter_exists_le S (fun v a => s < (lowNbr a t v : ℝ))
    _ ≤ ∑ v : Fin N, (1 / s) * (Real.exp (lam * t) * (m * Q)) := Finset.sum_le_sum (fun v _ => hv v)
    _ = N / s * (Real.exp (lam * t) * (m * Q)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

lemma choose_rel (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    ((m - 1).choose (k - 1) : ℝ) * m = k * (m.choose k : ℝ) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have := Nat.add_one_mul_choose_eq m' k'
  simp only [Nat.add_sub_cancel]
  have h : ((m' + 1 : ℕ) : ℝ) * (m'.choose k' : ℝ) = ((m' + 1).choose (k' + 1) : ℝ) * ((k' + 1 : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at h ⊢
  linarith

/-- Normalised probability bound for Lemma A.5. -/
lemma prob_bound_A5 (N m k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) (hkm : k ≤ m) (s ε : ℝ) (hs : 0 < s)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (((Fintype.piFinset (fun _ : Fin N => rowSet m k)).filter
        (fun a => ∃ v, s < (lowNbr a ((1 - ε) * ((N : ℝ) * k / m)) v : ℝ))).card : ℝ)
        / ((m.choose k : ℝ) ^ N)
      ≤ N / s * k * Real.exp (-(((N : ℝ) * k / m) * ε ^ 2 / 4)) := by
  have hm : 1 ≤ m := le_trans hk hkm
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hC : (0:ℝ) < (m.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkm
  set μ : ℝ := (N : ℝ) * k / m with hμ
  set p : ℝ := (k : ℝ) / m with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hmr]; exact_mod_cast hkm
  set y := Real.exp (-ε) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : y ≤ 1 := by rw [hy]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hD : ((m - 1).choose (k - 1) : ℝ) = p * (m.choose k : ℝ) := by
    have := choose_rel m k hk hkm
    rw [hp]; field_simp; linarith
  have h1 := count_bad_A5 N m k hk s ((1 - ε) * μ) ε hs hε0.le
  rw [hD] at h1
  have e1 : (y * (p * (m.choose k : ℝ)) + ((m.choose k : ℝ) - p * (m.choose k : ℝ))) ^ (N - 1)
      = (m.choose k : ℝ) ^ (N - 1) * (1 - p + p * y) ^ (N - 1) := by
    rw [← mul_pow]; congr 1; ring
  rw [e1] at h1
  have e2 : (m : ℝ) * (y * (p * (m.choose k : ℝ)) * ((m.choose k : ℝ) ^ (N - 1) * (1 - p + p * y) ^ (N - 1)))
      = (m.choose k : ℝ) ^ N * (k * y * (1 - p + p * y) ^ (N - 1)) := by
    have : (m.choose k : ℝ) ^ N = (m.choose k : ℝ) * (m.choose k : ℝ) ^ (N - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, hp]; field_simp
  rw [e2] at h1
  rw [div_le_iff₀ (pow_pos hC N)]
  refine h1.trans ?_
  -- now bound the analytic part
  have hbase0 : 0 ≤ 1 - p + p * y := by nlinarith
  have hbase : 1 - p + p * y ≤ Real.exp (-(p * (1 - y))) := by
    have := Real.add_one_le_exp (-(p * (1 - y))); linarith
  have hpow : (1 - p + p * y) ^ (N - 1) ≤ Real.exp (-(p * (1 - y))) ^ (N - 1) :=
    pow_le_pow_left₀ hbase0 hbase _
  rw [← Real.exp_nat_mul] at hpow
  have hquad : y ≤ 1 - ε + 3 / 4 * ε ^ 2 := by
    have := exp_le_quad (x := -ε) (by rw [abs_neg, abs_of_pos hε0]; exact hε1)
    rw [hy]; nlinarith
  have hy' : 1 - y ≤ ε := by
    have := Real.add_one_le_exp (-ε); rw [hy]; linarith
  have hNm1 : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub hN]; simp
  rw [hNm1] at hpow
  have hμp : ((N : ℝ) - 1) * p = μ - p := by rw [hμ, hp]; ring
  have hμ0 : 0 ≤ μ := by positivity
  -- exponent inequality
  have hexp : ε * ((1 - ε) * μ) + (-ε) + ((N : ℝ) - 1) * -(p * (1 - y)) ≤ -(μ * ε ^ 2 / 4) := by
    have : ((N : ℝ) - 1) * -(p * (1 - y)) = -(μ - p) * (1 - y) := by rw [← hμp]; ring
    rw [this]
    have h3 : p * (1 - y) ≤ ε := by nlinarith
    have h4 : μ * (ε - 3 / 4 * ε ^ 2) ≤ μ * (1 - y) := mul_le_mul_of_nonneg_left (by linarith) hμ0
    nlinarith
  have hfinal : Real.exp (ε * ((1 - ε) * μ)) * (k * y * (1 - p + p * y) ^ (N - 1))
      ≤ k * Real.exp (-(μ * ε ^ 2 / 4)) := by
    calc Real.exp (ε * ((1 - ε) * μ)) * (k * y * (1 - p + p * y) ^ (N - 1))
        ≤ Real.exp (ε * ((1 - ε) * μ)) * (k * y * Real.exp (((N : ℝ) - 1) * -(p * (1 - y)))) := by
          gcongr
      _ = k * Real.exp (ε * ((1 - ε) * μ) + (-ε) + ((N : ℝ) - 1) * -(p * (1 - y))) := by
          rw [Real.exp_add, Real.exp_add, hy]; ring
      _ ≤ k * Real.exp (-(μ * ε ^ 2 / 4)) := by gcongr
  have hNs : 0 ≤ (N : ℝ) / s := by positivity
  have hCN : 0 ≤ (m.choose k : ℝ) ^ N := by positivity
  calc (N : ℝ) / s * (Real.exp (ε * ((1 - ε) * μ)) * ((m.choose k : ℝ) ^ N *
        (k * y * (1 - p + p * y) ^ (N - 1))))
      = (N : ℝ) / s * (Real.exp (ε * ((1 - ε) * μ)) * (k * y * (1 - p + p * y) ^ (N - 1)))
          * (m.choose k : ℝ) ^ N := by ring
    _ ≤ (N : ℝ) / s * (k * Real.exp (-(μ * ε ^ 2 / 4))) * (m.choose k : ℝ) ^ N := by gcongr
    _ = N / s * k * Real.exp (-(μ * ε ^ 2 / 4)) * (m.choose k : ℝ) ^ N := by ring

/-- Deterministic step of Lemma A.5. -/
lemma det_A5 (N m k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) (hkm : k ≤ m)
    (a : Fin N → Fin m → Bool) (hreg : ∀ v, (Finset.univ.filter (fun w => a v w = true)).card = k)
    (e : ℝ) (he0 : 0 < e) (he1 : e ≤ 1) (v : Fin N)
    (hv : (lowNbr a ((1 - e / 4) * ((N : ℝ) * k / m)) v : ℝ) ≤ e * k / (2 * ((N : ℝ) * k / m))) :
    (N : ℝ) / m * ∑ w, (if a v w = true then ((col a w : ℕ) : ℝ)⁻¹ else 0) ≤ 1 + e := by
  classical
  have hm : 1 ≤ m := le_trans hk hkm
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  set μ : ℝ := (N : ℝ) * k / m with hμ
  have hμ0 : 0 < μ := by positivity
  set t : ℝ := (1 - e / 4) * μ with ht
  have ht0 : 0 < t := by have : 0 < 1 - e / 4 := by linarith
                         positivity
  have hterm : ∀ w, (if a v w = true then ((col a w : ℕ) : ℝ)⁻¹ else 0)
      ≤ (if a v w = true ∧ (col a w : ℝ) ≤ t then (1:ℝ) else 0)
        + (if a v w = true then t⁻¹ else 0) := by
    intro w
    by_cases h1 : a v w = true
    · have hc1 : 1 ≤ col a w := by
        unfold col
        exact Finset.card_pos.mpr ⟨v, by simp [h1]⟩
      have hc1r : (1:ℝ) ≤ col a w := by exact_mod_cast hc1
      rw [if_pos h1, if_pos h1]
      by_cases h2 : (col a w : ℝ) ≤ t
      · rw [if_pos ⟨h1, h2⟩]
        have : ((col a w : ℕ) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1r
        have : 0 ≤ t⁻¹ := by positivity
        linarith
      · rw [if_neg (fun h => h2 h.2)]
        push_neg at h2
        have := (inv_lt_inv₀ (lt_trans ht0 h2) ht0).mpr h2
        linarith
    · rw [if_neg h1, if_neg h1, if_neg (fun h => h1 h.1)]; simp
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hterm w)
  rw [Finset.sum_add_distrib] at hsum
  have hL : ∑ w, (if a v w = true ∧ (col a w : ℝ) ≤ t then (1:ℝ) else 0)
      = (lowNbr a t v : ℝ) := by
    rw [lowNbr, Finset.card_filter]; push_cast; rfl
  have hK : ∑ w, (if a v w = true then t⁻¹ else 0) = k * t⁻¹ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hreg v]
  rw [hL, hK] at hsum
  have hNm : (0:ℝ) ≤ N / m := by positivity
  calc (N : ℝ) / m * ∑ w, (if a v w = true then ((col a w : ℕ) : ℝ)⁻¹ else 0)
      ≤ (N : ℝ) / m * ((lowNbr a t v : ℝ) + k * t⁻¹) := mul_le_mul_of_nonneg_left hsum hNm
    _ ≤ (N : ℝ) / m * (e * k / (2 * μ) + k * t⁻¹) := by gcongr
    _ = e / 2 + (1 - e / 4)⁻¹ := by
        rw [ht, hμ]; field_simp
    _ ≤ 1 + e := by
        have h4 : 0 < 1 - e / 4 := by linarith
        have : 1 ≤ (1 - e / 4) * (1 + e / 2) := by nlinarith
        have h5 : (1 - e / 4)⁻¹ ≤ 1 + e / 2 := by
          rw [inv_le_iff_one_le_mul₀ h4]; linarith
        linarith

end StrictCompatLB.RegularDegree.RDInfra

namespace StrictCompatLB.RegularDegree.RDBinom

/-- Binomial probability mass. -/
noncomputable def bterm (m : ℕ) (p : ℝ) (j : ℕ) : ℝ := (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)

lemma bterm_nonneg (m : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) : 0 ≤ bterm m p j := by
  unfold bterm; have : 0 ≤ 1 - p := by linarith
  positivity

lemma sum_bterm (m : ℕ) (p : ℝ) : ∑ j ∈ Finset.range (m + 1), bterm m p j = 1 := by
  have := (add_pow p (1 - p) m).symm
  rw [show p + (1 - p) = 1 by ring, one_pow] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro j _; unfold bterm; ring

lemma upper_tail (m : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s lam : ℝ) (hlam : 0 ≤ lam) :
    ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => s ≤ (j : ℝ)), bterm m p j
      ≤ Real.exp (-(lam * s)) * (1 - p + p * Real.exp lam) ^ m := by
  have hq : 0 ≤ 1 - p := by linarith
  calc ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => s ≤ (j : ℝ)), bterm m p j
      ≤ ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => s ≤ (j : ℝ)),
          Real.exp (-(lam * s)) * ((m.choose j : ℝ) * (p * Real.exp lam) ^ j * (1 - p) ^ (m - j)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := (Finset.mem_filter.mp hj).2
        unfold bterm
        have h1 : 1 ≤ Real.exp (-(lam * s)) * Real.exp lam ^ j := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          apply Real.one_le_exp; nlinarith
        have h2 : 0 ≤ (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) := by positivity
        calc (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)
            ≤ (Real.exp (-(lam * s)) * Real.exp lam ^ j) * ((m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)) :=
              le_mul_of_one_le_left h2 h1
          _ = _ := by rw [mul_pow]; ring
    _ ≤ ∑ j ∈ Finset.range (m + 1),
          Real.exp (-(lam * s)) * ((m.choose j : ℝ) * (p * Real.exp lam) ^ j * (1 - p) ^ (m - j)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro j _ _; positivity
    _ = Real.exp (-(lam * s)) * (1 - p + p * Real.exp lam) ^ m := by
        rw [← Finset.mul_sum]
        congr 1
        rw [show 1 - p + p * Real.exp lam = p * Real.exp lam + (1 - p) by ring, add_pow]
        apply Finset.sum_congr rfl
        intro j _; ring

lemma bterm_succ (m : ℕ) (p : ℝ) (j : ℕ) (hj : j < m) :
    bterm m p (j + 1) * ((j + 1 : ℝ) * (1 - p)) = bterm m p j * (((m - j : ℕ) : ℝ) * p) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = j + 1 + q := ⟨m - (j + 1), by omega⟩
  unfold bterm
  have hc := Nat.choose_succ_right_eq (j + 1 + q) j
  have e1 : j + 1 + q - j = q + 1 := by omega
  have e2 : j + 1 + q - (j + 1) = q := by omega
  rw [e1] at hc
  rw [e1, e2]
  have hc' : ((j + 1 + q).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
      = ((j + 1 + q).choose j : ℝ) * ((q : ℝ) + 1) := by exact_mod_cast hc
  push_cast
  linear_combination (p ^ j * p * (1 - p) ^ q * (1 - p)) * hc'

/-- Unimodality: with `p = k/m`, the binomial mass is maximal at `k`. -/
lemma bterm_le_mode (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (j : ℕ) :
    bterm m ((k : ℝ) / m) j ≤ bterm m ((k : ℝ) / m) k := by
  have hm : 0 < m := by omega
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  set p : ℝ := (k : ℝ) / m with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hmr]; exact_mod_cast hkm
  -- increasing below k
  have hinc : ∀ i, i < k → bterm m p i ≤ bterm m p (i + 1) := by
    intro i hi
    by_cases hp1' : p = 1
    · -- then k = m, and bterm i = 0 for i < m
      have : bterm m p i = 0 := by
        unfold bterm; rw [hp1', sub_self, zero_pow (by omega)]; ring
      rw [this]; exact bterm_nonneg m hp0 hp1 _
    · have hq : 0 < 1 - p := by
        rcases lt_or_eq_of_le hp1 with h | h
        · linarith
        · exact absurd h hp1'
      have key := bterm_succ m p i (by omega)
      have hineq : ((i + 1 : ℝ) * (1 - p)) ≤ (((m - i : ℕ) : ℝ) * p) := by
        rw [Nat.cast_sub (by omega), hp]
        have hik : (i:ℝ) + 1 ≤ k := by exact_mod_cast hi
        field_simp
        have hkm' : (k:ℝ) ≤ m := by exact_mod_cast hkm
        nlinarith
      have h0 := bterm_nonneg m hp0 hp1 i
      have hpos : 0 < (i + 1 : ℝ) * (1 - p) := by positivity
      by_contra hcon
      push_neg at hcon
      have : bterm m p (i + 1) * ((i + 1 : ℝ) * (1 - p)) < bterm m p i * ((i + 1 : ℝ) * (1 - p)) :=
        mul_lt_mul_of_pos_right hcon hpos
      nlinarith
  -- decreasing from k
  have hdec : ∀ i, k ≤ i → bterm m p (i + 1) ≤ bterm m p i := by
    intro i hi
    by_cases him : i < m
    · have hq : 0 < 1 - p := by
        have : (k : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt hi him)
        rw [hp]; rw [sub_pos, div_lt_one hmr]; exact this
      have key := bterm_succ m p i him
      have hineq : (((m - i : ℕ) : ℝ) * p) ≤ ((i + 1 : ℝ) * (1 - p)) := by
        rw [Nat.cast_sub (by omega), hp]
        have hik : (k:ℝ) ≤ i := by exact_mod_cast hi
        field_simp
        have hkm' : (k:ℝ) ≤ m := by exact_mod_cast hkm
        nlinarith
      have h0 := bterm_nonneg m hp0 hp1 i
      have hpos : 0 < (i + 1 : ℝ) * (1 - p) := by positivity
      have : bterm m p (i + 1) * ((i + 1 : ℝ) * (1 - p)) ≤ bterm m p i * ((i + 1 : ℝ) * (1 - p)) := by
        rw [key]; exact mul_le_mul_of_nonneg_left hineq h0
      exact le_of_mul_le_mul_right this hpos
    · have : bterm m p (i + 1) = 0 := by
        unfold bterm; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      rw [this]; exact bterm_nonneg m hp0 hp1 _
  have up : ∀ d i, i + d = k → bterm m p i ≤ bterm m p k := by
    intro d
    induction d with
    | zero => intro i h; simp at h; rw [h]
    | succ d ih =>
      intro i h
      exact (hinc i (by omega)).trans (ih (i + 1) (by omega))
  have down : ∀ d, bterm m p (k + d) ≤ bterm m p k := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => exact (hdec (k + d) (by omega)).trans ih
  rcases le_or_gt j k with hjk | hjk
  · exact up (k - j) j (by omega)
  · have := down (j - k)
    rwa [show k + (j - k) = j by omega] at this

lemma mode_lower (m k : ℕ) (hk : 3 ≤ k) (hkm : k ≤ m) :
    1 / (4 * (k : ℝ)) ≤ bterm m ((k : ℝ) / m) k := by
  have hm : 0 < m := by omega
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hkr : (3:ℝ) ≤ k := by exact_mod_cast hk
  set p : ℝ := (k : ℝ) / m with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hmr]; exact_mod_cast hkm
  have htot := sum_bterm m p
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m + 1))
    (fun j : ℕ => (2 * (k:ℝ)) ≤ (j : ℝ))] at htot
  have hup := upper_tail m hp0 hp1 (2 * (k:ℝ)) 1 zero_le_one
  have hbase : 1 - p + p * Real.exp 1 ≤ Real.exp (p * (Real.exp 1 - 1)) := by
    have := Real.add_one_le_exp (p * (Real.exp 1 - 1)); linarith
  have hb0 : 0 ≤ 1 - p + p * Real.exp 1 := by
    have := Real.exp_pos 1; nlinarith
  have hpow : (1 - p + p * Real.exp 1) ^ m ≤ Real.exp (p * (Real.exp 1 - 1)) ^ m :=
    pow_le_pow_left₀ hb0 hbase m
  rw [← Real.exp_nat_mul] at hpow
  have hmp : (m : ℝ) * (p * (Real.exp 1 - 1)) = k * (Real.exp 1 - 1) := by
    rw [hp]; field_simp
  rw [hmp] at hpow
  have he := Real.exp_one_lt_d9
  have hl := Real.log_two_lt_d9
  have htail : Real.exp (-(1 * (2 * (k:ℝ)))) * (1 - p + p * Real.exp 1) ^ m ≤ 1 / 2 := by
    calc Real.exp (-(1 * (2 * (k:ℝ)))) * (1 - p + p * Real.exp 1) ^ m
        ≤ Real.exp (-(1 * (2 * (k:ℝ)))) * Real.exp (k * (Real.exp 1 - 1)) := by gcongr
      _ = Real.exp ((k:ℝ) * (Real.exp 1 - 3)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ 1 / 2 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
          have h2 : (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          rw [h2, ← Real.exp_add]
          apply Real.exp_le_one_iff.mpr
          have : (k:ℝ) * (Real.exp 1 - 3) ≤ 3 * (Real.exp 1 - 3) := by nlinarith
          linarith
  have hlow : ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ¬ (2 * (k:ℝ)) ≤ (j : ℝ)),
      bterm m p j ≤ (2 * (k:ℝ)) * bterm m p k := by
    calc ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ¬ (2 * (k:ℝ)) ≤ (j : ℝ)), bterm m p j
        ≤ ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ¬ (2 * (k:ℝ)) ≤ (j : ℝ)), bterm m p k :=
          Finset.sum_le_sum (fun j _ => bterm_le_mode m k (by omega) hkm j)
      _ = ((Finset.range (m + 1)).filter (fun j : ℕ => ¬ (2 * (k:ℝ)) ≤ (j : ℝ))).card * bterm m p k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (k:ℝ)) * bterm m p k := by
          apply mul_le_mul_of_nonneg_right _ (bterm_nonneg m hp0 hp1 k)
          have : (Finset.range (m + 1)).filter (fun j : ℕ => ¬ (2 * (k:ℝ)) ≤ (j : ℝ))
              ⊆ Finset.range (2 * k) := by
            intro j hj
            have := (Finset.mem_filter.mp hj).2
            push_neg at this
            rw [Finset.mem_range]
            exact_mod_cast this
          have := Finset.card_le_card this
          rw [Finset.card_range] at this
          exact_mod_cast this
  have : 1 / 2 ≤ (2 * (k:ℝ)) * bterm m p k := by linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

end StrictCompatLB.RegularDegree.RDBinom

namespace StrictCompatLB.RegularDegree.RDInfra

open StrictCompatLB.MeanField StrictCompatLB.RegularDegree StrictCompatLB.RegularDegree.RDBinom

/-- Number of entries of the row `r` lying in `X`. -/
def rowHits {m : ℕ} (r : Fin m → Bool) (X : Finset (Fin m)) : ℕ :=
  (Finset.univ.filter (fun w => r w = true) ∩ X).card

lemma gen_bound (m k : ℕ) (X : Finset (Fin m)) (p y : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hy : 0 ≤ y) :
    p ^ k * (1 - p) ^ (m - k) * ∑ r ∈ rowSet m k, y ^ rowHits r X
      ≤ (1 - p + p * y) ^ X.card := by
  classical
  have hq : 0 ≤ 1 - p := by linarith
  let g : Fin m → ℝ := fun j => if j ∈ X then y else 1
  let f : Fin m → Bool → ℝ := fun j b => if b = true then p * g j else 1 - p
  have hf0 : ∀ j b, 0 ≤ f j b := by
    intro j b; simp only [f, g]; split_ifs <;> positivity
  have hrow : ∀ r ∈ rowSet m k, p ^ k * (1 - p) ^ (m - k) * y ^ rowHits r X = ∏ j, f j (r j) := by
    intro r hr
    have hr' : (Finset.univ.filter (fun w => r w = true)).card = k := by
      simpa [rowSet] using hr
    simp only [f]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_const]
    have hcomp : (Finset.univ.filter (fun j => ¬ r j = true)).card = m - k := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
        (fun j => r j = true)
      rw [Finset.card_univ, Fintype.card_fin, hr'] at this
      omega
    have hg : ∏ j ∈ Finset.univ.filter (fun j => r j = true), g j = y ^ rowHits r X := by
      simp only [g]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, rowHits,
        Finset.filter_mem_eq_inter]
    rw [hg, hr', hcomp]; ring
  have hall : ∑ r : Fin m → Bool, ∏ j, f j (r j) = (1 - p + p * y) ^ X.card := by
    have := (Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset Bool)) f).symm
    rw [Fintype.piFinset_univ] at this
    rw [this]
    have h2 : ∀ j, ∑ b ∈ (Finset.univ : Finset Bool), f j b = if j ∈ X then 1 - p + p * y else 1 := by
      intro j
      simp only [f, g, Fintype.sum_bool]
      by_cases hj : j ∈ X
      · simp only [if_pos hj]; simp; ring
      · simp only [if_neg hj]; simp
    simp_rw [h2]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.mul_sum]
  calc ∑ r ∈ rowSet m k, p ^ k * (1 - p) ^ (m - k) * y ^ rowHits r X
      = ∑ r ∈ rowSet m k, ∏ j, f j (r j) := Finset.sum_congr rfl hrow
    _ ≤ ∑ r : Fin m → Bool, ∏ j, f j (r j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun r _ _ => Finset.prod_nonneg (fun j _ => hf0 j (r j)))
    _ = (1 - p + p * y) ^ X.card := hall

/-- Bad rows for `X`. -/
noncomputable def badRow (m k : ℕ) (ε : ℝ) (X : Finset (Fin m)) : Finset (Fin m → Bool) :=
  (rowSet m k).filter (fun r => ε * (k : ℝ) * (X.card : ℝ) / (m : ℝ) ≤
    |(rowHits r X : ℝ) - (k : ℝ) * (X.card : ℝ) / (m : ℝ)|)

lemma badRow_bound (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 3 / 2)
    (X : Finset (Fin m)) :
    ((badRow m k ε X).card : ℝ) * (((k : ℝ) / m) ^ k * (1 - (k : ℝ) / m) ^ (m - k))
      ≤ 2 * Real.exp (-(5 * ε ^ 2 / 16 * ((k : ℝ) * X.card / m))) := by
  classical
  have hm : 0 < m := by omega
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  set p : ℝ := (k : ℝ) / m with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hmr]; exact_mod_cast hkm
  have hq : 0 ≤ 1 - p := by linarith
  set w0 : ℝ := p ^ k * (1 - p) ^ (m - k) with hw0
  have hw00 : 0 ≤ w0 := by positivity
  set K : ℝ := (X.card : ℝ)
  set mu : ℝ := p * K with hmu
  have hmu0 : 0 ≤ mu := by positivity
  set lam : ℝ := ε / 2 with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : |lam| ≤ 1 := by rw [abs_of_nonneg hlam0]; linarith
  have hlam1' : |-lam| ≤ 1 := by rw [abs_neg]; exact hlam1
  -- pointwise: 1 ≤ e^{λ(n - (1+ε)mu)} + e^{λ((1-ε)mu - n)} for bad rows
  have hpt : ∀ r ∈ badRow m k ε X,
      (1:ℝ) ≤ Real.exp (-(lam * ((1 + ε) * mu))) * Real.exp lam ^ rowHits r X
        + Real.exp (lam * ((1 - ε) * mu)) * Real.exp (-lam) ^ rowHits r X := by
    intro r hr
    have hb := (Finset.mem_filter.mp hr).2
    have e1 : ε * (k : ℝ) * K / m = ε * mu := by rw [hmu, hp]; ring
    have e2 : (k : ℝ) * K / m = mu := by rw [hmu, hp]; ring
    rw [e1, e2] at hb
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    rcases le_abs'.mp hb with h | h
    · have : 0 ≤ lam * ((1 - ε) * mu) + (rowHits r X : ℝ) * -lam := by nlinarith
      have := Real.one_le_exp this
      have := Real.exp_pos (-(lam * ((1 + ε) * mu)) + (rowHits r X : ℝ) * lam)
      linarith
    · have : 0 ≤ -(lam * ((1 + ε) * mu)) + (rowHits r X : ℝ) * lam := by nlinarith
      have := Real.one_le_exp this
      have := Real.exp_pos (lam * ((1 - ε) * mu) + (rowHits r X : ℝ) * -lam)
      linarith
  have hsum : ((badRow m k ε X).card : ℝ)
      ≤ Real.exp (-(lam * ((1 + ε) * mu))) * ∑ r ∈ rowSet m k, Real.exp lam ^ rowHits r X
        + Real.exp (lam * ((1 - ε) * mu)) * ∑ r ∈ rowSet m k, Real.exp (-lam) ^ rowHits r X := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc ((badRow m k ε X).card : ℝ) = ∑ r ∈ badRow m k ε X, (1:ℝ) := by simp
      _ ≤ ∑ r ∈ badRow m k ε X, (Real.exp (-(lam * ((1 + ε) * mu))) * Real.exp lam ^ rowHits r X
          + Real.exp (lam * ((1 - ε) * mu)) * Real.exp (-lam) ^ rowHits r X) :=
          Finset.sum_le_sum hpt
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun r _ _ => by positivity)
  have hg1 := gen_bound m k X p (Real.exp lam) hp0 hp1 (Real.exp_pos _).le
  have hg2 := gen_bound m k X p (Real.exp (-lam)) hp0 hp1 (Real.exp_pos _).le
  -- (1 - p + p e^{±λ})^K ≤ exp(p K (±λ + 3/4 λ²))
  have hpow : ∀ x : ℝ, |x| ≤ 1 → (1 - p + p * Real.exp x) ^ X.card
      ≤ Real.exp (mu * (x + 3 / 4 * x ^ 2)) := by
    intro x hx
    have h1 : 1 - p + p * Real.exp x ≤ Real.exp (p * (x + 3 / 4 * x ^ 2)) := by
      have := exp_le_quad hx
      have h2 := Real.add_one_le_exp (p * (x + 3 / 4 * x ^ 2))
      nlinarith
    have h0 : 0 ≤ 1 - p + p * Real.exp x := by have := Real.exp_pos x; nlinarith
    calc (1 - p + p * Real.exp x) ^ X.card ≤ Real.exp (p * (x + 3 / 4 * x ^ 2)) ^ X.card :=
          pow_le_pow_left₀ h0 h1 _
      _ = Real.exp (mu * (x + 3 / 4 * x ^ 2)) := by
          rw [← Real.exp_nat_mul, hmu]; congr 1; ring
  have hA := hpow lam hlam1
  have hB := hpow (-lam) hlam1'
  calc ((badRow m k ε X).card : ℝ) * w0
      ≤ (Real.exp (-(lam * ((1 + ε) * mu))) * ∑ r ∈ rowSet m k, Real.exp lam ^ rowHits r X
        + Real.exp (lam * ((1 - ε) * mu)) * ∑ r ∈ rowSet m k, Real.exp (-lam) ^ rowHits r X) * w0 :=
        mul_le_mul_of_nonneg_right hsum hw00
    _ = Real.exp (-(lam * ((1 + ε) * mu))) * (w0 * ∑ r ∈ rowSet m k, Real.exp lam ^ rowHits r X)
        + Real.exp (lam * ((1 - ε) * mu)) * (w0 * ∑ r ∈ rowSet m k, Real.exp (-lam) ^ rowHits r X) := by
        ring
    _ ≤ Real.exp (-(lam * ((1 + ε) * mu))) * Real.exp (mu * (lam + 3 / 4 * lam ^ 2))
        + Real.exp (lam * ((1 - ε) * mu)) * Real.exp (mu * (-lam + 3 / 4 * (-lam) ^ 2)) := by
        gcongr
        · exact hg1.trans hA
        · exact hg2.trans hB
    _ = 2 * Real.exp (-(5 * ε ^ 2 / 16 * ((k : ℝ) * X.card / m))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        have e3 : (k : ℝ) * X.card / m = mu := by rw [hmu, hp]; ring
        rw [e3]
        have e4 : -(lam * ((1 + ε) * mu)) + mu * (lam + 3 / 4 * lam ^ 2)
            = -(5 * ε ^ 2 / 16 * mu) := by rw [hlam]; ring
        have e5 : lam * ((1 - ε) * mu) + mu * (-lam + 3 / 4 * (-lam) ^ 2)
            = -(5 * ε ^ 2 / 16 * mu) := by rw [hlam]; ring
        rw [e4, e5]; ring

/-- Bad servers of a matrix for `X`. -/
noncomputable def badSrv {N m : ℕ} (k : ℕ) (ε : ℝ) (a : Fin N → Fin m → Bool) (X : Finset (Fin m)) :
    Finset (Fin N) :=
  Finset.univ.filter (fun v => ε * (k : ℝ) * (X.card : ℝ) / (m : ℝ) ≤
    |(rowHits (a v) X : ℝ) - (k : ℝ) * (X.card : ℝ) / (m : ℝ)|)

lemma count_bad_A2 (N m k : ℕ) (hC : 0 < m.choose k) (ε η δ θ : ℝ) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ)
    (hρ : ∀ X : Finset (Fin m), η * m ≤ (X.card : ℝ) →
      ((badRow m k ε X).card : ℝ) / (m.choose k : ℝ) ≤ Real.exp (-θ)) :
    (((Fintype.piFinset (fun _ : Fin N => rowSet m k)).filter
        (fun a => ∃ X : Finset (Fin m), η * m ≤ (X.card : ℝ) ∧
          δ * N < ((badSrv k ε a X).card : ℝ))).card : ℝ) / ((m.choose k : ℝ) ^ N)
      ≤ 2 ^ m * 2 ^ N * Real.exp (-(θ * (δ * N))) := by
  classical
  set R := rowSet m k
  set C : ℝ := (m.choose k : ℝ)
  have hCr : 0 < C := Nat.cast_pos.mpr hC
  set big := (Finset.univ : Finset (Finset (Fin m))).filter (fun X => η * m ≤ (X.card : ℝ))
  set Ts := (Finset.univ : Finset (Finset (Fin N))).filter (fun T => δ * N < (T.card : ℝ))
  let box : Finset (Fin m) → Finset (Fin N) → Finset (Fin N → Fin m → Bool) := fun X T =>
    Fintype.piFinset (fun v => if v ∈ T then badRow m k ε X else R)
  have hsub : (Fintype.piFinset (fun _ : Fin N => R)).filter
        (fun a => ∃ X : Finset (Fin m), η * m ≤ (X.card : ℝ) ∧
          δ * N < ((badSrv k ε a X).card : ℝ))
      ⊆ big.biUnion (fun X => Ts.biUnion (fun T => box X T)) := by
    intro a ha
    obtain ⟨haR, X, hX, hB⟩ := Finset.mem_filter.mp ha
    rw [Fintype.mem_piFinset] at haR
    simp only [Finset.mem_biUnion]
    refine ⟨X, by simp [big, hX], badSrv k ε a X, by simp [Ts, hB], ?_⟩
    simp only [box, Fintype.mem_piFinset]
    intro v
    split_ifs with hv
    · simp only [badRow, Finset.mem_filter]
      refine ⟨haR v, ?_⟩
      simpa [badSrv] using hv
    · exact haR v
  have hbox : ∀ X T, ((box X T).card : ℝ) = ((badRow m k ε X).card : ℝ) ^ T.card * C ^ (N - T.card) := by
    intro X T
    simp only [box, Fintype.card_piFinset]
    push_cast
    have hite : ∀ i : Fin N, (((if i ∈ T then badRow m k ε X else R).card : ℕ) : ℝ)
        = if i ∈ T then ((badRow m k ε X).card : ℝ) else C := by
      intro i; split_ifs
      · rfl
      · simp only [R, C, card_rowSet]
    simp_rw [hite]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have : (Finset.univ.filter (fun v : Fin N => v ∉ T)).card = N - T.card := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp
    rw [this]
    congr 2
    simp
  have hbox' : ∀ X ∈ big, ∀ T ∈ Ts, ((box X T).card : ℝ) / C ^ N ≤ Real.exp (-(θ * (δ * N))) := by
    intro X hX T hT
    have hX' : η * m ≤ (X.card : ℝ) := (Finset.mem_filter.mp hX).2
    have hT' : δ * N < (T.card : ℝ) := (Finset.mem_filter.mp hT).2
    have hTN : T.card ≤ N := by simpa using Finset.card_le_univ T
    rw [hbox]
    have e1 : ((badRow m k ε X).card : ℝ) ^ T.card * C ^ (N - T.card) / C ^ N
        = (((badRow m k ε X).card : ℝ) / C) ^ T.card := by
      rw [div_pow]
      have : C ^ N = C ^ T.card * C ^ (N - T.card) := by rw [← pow_add]; congr 1; omega
      rw [this]; field_simp
    rw [e1]
    have h0 : 0 ≤ ((badRow m k ε X).card : ℝ) / C := by positivity
    calc (((badRow m k ε X).card : ℝ) / C) ^ T.card ≤ Real.exp (-θ) ^ T.card :=
          pow_le_pow_left₀ h0 (hρ X hX') _
      _ = Real.exp (-(θ * T.card)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (-(θ * (δ * N))) := by
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left hT'.le hθ
          linarith
  have hcard := Finset.card_le_card hsub
  have h1 : (((Fintype.piFinset (fun _ : Fin N => R)).filter
        (fun a => ∃ X : Finset (Fin m), η * m ≤ (X.card : ℝ) ∧
          δ * N < ((badSrv k ε a X).card : ℝ))).card : ℝ)
      ≤ ∑ X ∈ big, ∑ T ∈ Ts, ((box X T).card : ℝ) := by
    calc _ ≤ ((big.biUnion (fun X => Ts.biUnion (fun T => box X T))).card : ℝ) := by
          exact_mod_cast hcard
      _ ≤ ∑ X ∈ big, ((Ts.biUnion (fun T => box X T)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ X ∈ big, ∑ T ∈ Ts, ((box X T).card : ℝ) := by
          apply Finset.sum_le_sum; intro X _
          exact_mod_cast Finset.card_biUnion_le
  rw [div_le_iff₀ (pow_pos hCr N)]
  calc _ ≤ ∑ X ∈ big, ∑ T ∈ Ts, ((box X T).card : ℝ) := h1
    _ ≤ ∑ X ∈ big, ∑ T ∈ Ts, Real.exp (-(θ * (δ * N))) * C ^ N := by
        apply Finset.sum_le_sum; intro X hX
        apply Finset.sum_le_sum; intro T hT
        have := hbox' X hX T hT
        rwa [div_le_iff₀ (pow_pos hCr N)] at this
    _ = (big.card : ℝ) * ((Ts.card : ℝ) * (Real.exp (-(θ * (δ * N))) * C ^ N)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ m * (2 ^ N * (Real.exp (-(θ * (δ * N))) * C ^ N)) := by
        have hb : (big.card : ℝ) ≤ 2 ^ m := by
          have := Finset.card_le_univ big
          rw [Fintype.card_finset, Fintype.card_fin] at this
          exact_mod_cast this
        have ht : (Ts.card : ℝ) ≤ 2 ^ N := by
          have := Finset.card_le_univ Ts
          rw [Fintype.card_finset, Fintype.card_fin] at this
          exact_mod_cast this
        gcongr
    _ = 2 ^ m * 2 ^ N * Real.exp (-(θ * (δ * N))) * C ^ N := by ring

end StrictCompatLB.RegularDegree.RDInfra

open StrictCompatLB.RegularDegree StrictCompatLB.MeanField StrictCompatLB.RegularDegree.RDInfra
  StrictCompatLB.RegularDegree.RDBinom in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (hc : Tendsto (fun N : ℕ => (c N : ℝ)) atTop atTop)
    (hNcM : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / (M N : ℝ)) atTop atTop)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 3 / 2) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (η : ℝ) (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ X : Finset (Fin (M N)),
      η * (M N : ℝ) ≤ (X.card : ℝ) →
        ((badServers M c (randomGraph M adj ω) ε N X).card : ℝ) ≤ δ * (N : ℝ) := by
  classical
  -- regularity almost surely
  have hreg : ∀ᵐ ω ∂P, ∀ N, ∀ v : Fin N,
      (Finset.univ.filter (fun w => adj N ω v w = true)).card = c N := by
    rw [ae_all_iff]
    intro N
    rw [ae_iff]
    have hsub : {ω | ¬ ∀ v : Fin N, (Finset.univ.filter (fun w => adj N ω v w = true)).card = c N}
        ⊆ ⋃ a ∈ {a : Fin N → Fin (M N) → Bool | ¬ IsServerRegular (c N) a}, adj N ⁻¹' {a} := by
      intro ω hω
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨adj N ω, hω, rfl⟩
    apply measure_mono_null hsub
    rw [measure_biUnion_null_iff (Set.to_countable _)]
    intro a ha
    rw [(hadj N).2 a, if_neg ha]
  set κ : ℝ := 5 * ε ^ 2 / 16 * η with hκ
  have hκ0 : 0 < κ := by positivity
  -- eventual conditions
  have ev1 : ∀ᶠ N : ℕ in atTop, (3:ℝ) ≤ c N := hc.eventually (eventually_ge_atTop _)
  have ev2 : ∀ᶠ N : ℕ in atTop, 8 / (κ * δ) ≤ (c N : ℝ) := hc.eventually (eventually_ge_atTop _)
  have ev3 : ∀ᶠ N : ℕ in atTop, 4 / (κ * δ) ≤ (N : ℝ) * (c N : ℝ) / (M N : ℝ) :=
    hNcM.eventually (eventually_ge_atTop _)
  have ev4 : ∀ᶠ N : ℕ in atTop, 8 * (c N : ℝ) ≤ Real.exp (κ * c N / 4) := by
    have ht : Tendsto (fun N : ℕ => κ / 4 * (c N : ℝ)) atTop atTop :=
      hc.const_mul_atTop (by positivity)
    have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ht
    have h1 : ∀ᶠ N : ℕ in atTop, ((fun x : ℝ => x ^ 1 * Real.exp (-x)) ∘
        (fun N : ℕ => κ / 4 * (c N : ℝ))) N < κ / 32 :=
      h0.eventually (gt_mem_nhds (by positivity))
    filter_upwards [h1] with N hN
    simp only [Function.comp, pow_one] at hN
    have hE := Real.exp_pos (κ / 4 * (c N : ℝ))
    have : κ / 4 * (c N : ℝ) ≤ κ / 32 * Real.exp (κ / 4 * (c N : ℝ)) := by
      have e : Real.exp (-(κ / 4 * (c N : ℝ))) * Real.exp (κ / 4 * (c N : ℝ)) = 1 := by
        rw [← Real.exp_add]; simp
      have h := mul_lt_mul_of_pos_right hN hE
      rw [mul_assoc, e, mul_one] at h
      linarith
    have e2 : κ * c N / 4 = κ / 4 * (c N : ℝ) := by ring
    rw [e2]
    have h8 : 8 * (c N : ℝ) = (32 / κ) * (κ / 4 * (c N : ℝ)) := by field_simp; ring
    have h9 : (32 / κ) * (κ / 32 * Real.exp (κ / 4 * (c N : ℝ))) = Real.exp (κ / 4 * (c N : ℝ)) := by
      field_simp
    rw [h8, ← h9]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (ev1.and (ev2.and (ev3.and ev4)))
  let E : (N : ℕ) → Finset (Fin N → Fin (M N) → Bool) := fun N =>
    Finset.univ.filter (fun a => ∃ X : Finset (Fin (M N)), η * (M N : ℝ) ≤ (X.card : ℝ) ∧
      δ * N < ((badSrv (c N) ε a X).card : ℝ))
  have hbound : ∀ N ≥ max N₁ 1, P (adj N ⁻¹' (E N : Set _)) ≤ ENNReal.ofReal (Real.exp (-(N : ℝ))) := by
    intro N hN
    obtain ⟨h1, h2, h3, h4⟩ := hN₁ N (le_trans (le_max_left _ _) hN)
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hk := hc_pos N
    have hkm := hcM N
    have hm : 1 ≤ M N := le_trans hk hkm
    have hNr : (0:ℝ) < N := by exact_mod_cast hN1
    have hmr : (0:ℝ) < M N := by exact_mod_cast hm
    have hkr : (0:ℝ) < c N := by exact_mod_cast hk
    have hk3 : 3 ≤ c N := by exact_mod_cast h1
    have hC := Nat.choose_pos hkm
    have hCr : (0:ℝ) < ((M N).choose (c N) : ℝ) := Nat.cast_pos.mpr hC
    set θ : ℝ := 3 / 4 * κ * c N with hθ
    have hθ0 : 0 ≤ θ := by positivity
    -- per-row bound
    have hρ : ∀ X : Finset (Fin (M N)), η * (M N : ℝ) ≤ (X.card : ℝ) →
        ((badRow (M N) (c N) ε X).card : ℝ) / ((M N).choose (c N) : ℝ) ≤ Real.exp (-θ) := by
      intro X hX
      have hb := badRow_bound (M N) (c N) hk hkm ε hε0 hε X
      have hmode := mode_lower (M N) (c N) hk3 hkm
      unfold bterm at hmode
      set w0 : ℝ := ((c N : ℝ) / M N) ^ c N * (1 - (c N : ℝ) / M N) ^ (M N - c N)
      have hw : 1 / (4 * (c N : ℝ)) ≤ ((M N).choose (c N) : ℝ) * w0 := by
        have : ((M N).choose (c N) : ℝ) * ((c N : ℝ) / M N) ^ c N * (1 - (c N : ℝ) / M N) ^ (M N - c N)
            = ((M N).choose (c N) : ℝ) * w0 := by simp only [w0]; ring
        linarith
      have hX' : η * (c N : ℝ) ≤ (c N : ℝ) * X.card / M N := by
        rw [le_div_iff₀ hmr]
        have := mul_le_mul_of_nonneg_left hX hkr.le
        linarith
      have hexp : Real.exp (-(5 * ε ^ 2 / 16 * ((c N : ℝ) * X.card / M N)))
          ≤ Real.exp (-(κ * c N)) := by
        apply Real.exp_le_exp.mpr
        rw [hκ]
        have : 0 ≤ 5 * ε ^ 2 / 16 := by positivity
        have := mul_le_mul_of_nonneg_left hX' this
        linarith
      have hw0 : 0 < ((M N).choose (c N) : ℝ) * w0 := lt_of_lt_of_le (by positivity) hw
      -- #bad / C ≤ 2 exp(..) / (C w0) ≤ 8 c exp(-κ c)
      have step : ((badRow (M N) (c N) ε X).card : ℝ) / ((M N).choose (c N) : ℝ)
          ≤ 8 * c N * Real.exp (-(κ * c N)) := by
        rw [div_le_iff₀ hCr]
        have hb' : ((badRow (M N) (c N) ε X).card : ℝ) * w0 ≤ 2 * Real.exp (-(κ * c N)) :=
          hb.trans (by gcongr)
        -- multiply hb' by C, use C w0 ≥ 1/(4c)
        have hbad0 : 0 ≤ ((badRow (M N) (c N) ε X).card : ℝ) := by positivity
        have : ((badRow (M N) (c N) ε X).card : ℝ) * (1 / (4 * (c N : ℝ)))
            ≤ ((badRow (M N) (c N) ε X).card : ℝ) * (((M N).choose (c N) : ℝ) * w0) :=
          mul_le_mul_of_nonneg_left hw hbad0
        have h5 : ((badRow (M N) (c N) ε X).card : ℝ) * (((M N).choose (c N) : ℝ) * w0)
            ≤ ((M N).choose (c N) : ℝ) * (2 * Real.exp (-(κ * c N))) := by
          have := mul_le_mul_of_nonneg_left hb' hCr.le
          linarith
        have h6 : ((badRow (M N) (c N) ε X).card : ℝ) ≤
            4 * (c N : ℝ) * (((M N).choose (c N) : ℝ) * (2 * Real.exp (-(κ * c N)))) := by
          have h7 : ((badRow (M N) (c N) ε X).card : ℝ) * (1 / (4 * (c N : ℝ)))
              ≤ ((M N).choose (c N) : ℝ) * (2 * Real.exp (-(κ * c N))) := le_trans this h5
          rw [mul_one_div, div_le_iff₀ (by positivity)] at h7
          linarith
        linarith
      refine step.trans ?_
      -- 8 c exp(-κ c) ≤ exp(-θ)
      have e1 : Real.exp (-(κ * c N)) * Real.exp (κ * c N / 4) = Real.exp (-θ) := by
        rw [← Real.exp_add, hθ]; congr 1; ring
      rw [← e1]
      have := Real.exp_pos (-(κ * c N))
      have := mul_le_mul_of_nonneg_left h4 this.le
      linarith
    rw [prob_eq P M c adj hadj N (E N)]
    have hfilt : (E N).filter (fun a => IsServerRegular (c N) a)
        = (Fintype.piFinset (fun _ : Fin N => rowSet (M N) (c N))).filter
            (fun a => ∃ X : Finset (Fin (M N)), η * (M N : ℝ) ≤ (X.card : ℝ) ∧
              δ * N < ((badSrv (c N) ε a X).card : ℝ)) := by
      rw [← reg_eq_piFinset, Finset.filter_filter, Finset.filter_filter]
      apply Finset.filter_congr
      intro a _
      exact and_comm
    rw [hfilt]
    have hcnt := count_bad_A2 N (M N) (c N) hC ε η δ θ hθ0 hδ0.le hρ
    have hconv : (((Fintype.piFinset (fun _ : Fin N => rowSet (M N) (c N))).filter
            (fun a => ∃ X : Finset (Fin (M N)), η * (M N : ℝ) ≤ (X.card : ℝ) ∧
              δ * N < ((badSrv (c N) ε a X).card : ℝ))).card : ENNReal)
          * (((Nat.choose (M N) (c N) : ℕ) : ENNReal) ^ N)⁻¹
        = ENNReal.ofReal ((((Fintype.piFinset (fun _ : Fin N => rowSet (M N) (c N))).filter
            (fun a => ∃ X : Finset (Fin (M N)), η * (M N : ℝ) ≤ (X.card : ℝ) ∧
              δ * N < ((badSrv (c N) ε a X).card : ℝ))).card : ℝ) / (((M N).choose (c N) : ℝ) ^ N)) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow
        (by positivity), ENNReal.ofReal_natCast, div_eq_mul_inv]
    rw [hconv]
    apply ENNReal.ofReal_le_ofReal
    refine hcnt.trans ?_
    -- 2^m 2^N exp(-θ δ N) ≤ exp(-N)
    have h2e : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
    have hpm : (2:ℝ) ^ (M N) ≤ Real.exp (M N) := by
      calc (2:ℝ) ^ (M N) ≤ Real.exp 1 ^ (M N) := pow_le_pow_left₀ (by norm_num) h2e _
        _ = Real.exp (M N) := by rw [← Real.exp_nat_mul, mul_one]
    have hpN : (2:ℝ) ^ N ≤ Real.exp N := by
      calc (2:ℝ) ^ N ≤ Real.exp 1 ^ N := pow_le_pow_left₀ (by norm_num) h2e _
        _ = Real.exp N := by rw [← Real.exp_nat_mul, mul_one]
    have hmle : (M N : ℝ) ≤ κ * δ / 4 * (c N * N) := by
      have h3' := h3
      rw [div_le_div_iff₀ (by positivity) hmr] at h3'
      have hkd : 0 < κ * δ := by positivity
      have e : κ * δ / 4 * (c N * N) = (N * c N) * (κ * δ) / 4 := by ring
      rw [e, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
      linarith
    have hNle : 2 * (N : ℝ) ≤ κ * δ / 4 * (c N * N) := by
      have h2' := h2
      rw [div_le_iff₀ (by positivity)] at h2'
      have := mul_le_mul_of_nonneg_left h2' hNr.le
      have e : κ * δ / 4 * (c N * N) = (N : ℝ) * (c N * (κ * δ)) / 4 := by ring
      rw [e]
      linarith
    calc (2:ℝ) ^ (M N) * 2 ^ N * Real.exp (-(θ * (δ * N)))
        ≤ Real.exp (M N) * Real.exp N * Real.exp (-(θ * (δ * N))) := by gcongr
      _ = Real.exp ((M N : ℝ) + N - θ * (δ * N)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(N : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have e : θ * (δ * N) = 3 * (κ * δ / 4 * (c N * N)) := by rw [hθ]; ring
          rw [e]
          linarith
  filter_upwards [ae_eventually_of_le P (fun N => adj N ⁻¹' (E N : Set _)) _
    Real.summable_exp_neg_nat _ hbound, hreg] with ω hω hreg
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hω
  refine ⟨max N₀ 1, le_max_right _ _, fun N hN X hX => ?_⟩
  have hnot := hN₀ N (le_trans (le_max_left _ _) hN)
  by_contra hcon
  push_neg at hcon
  apply hnot
  simp only [Set.mem_preimage, Finset.coe_filter, Finset.mem_univ, true_and, E]
  refine ⟨X, hX, ?_⟩
  have : badServers M c (randomGraph M adj ω) ε N X = badSrv (c N) ε (adj N ω) X := by
    unfold badServers badSrv
    apply Finset.filter_congr
    intro v _
    have hn : nbrV M (randomGraph M adj ω) N v = Finset.univ.filter (fun w => adj N ω v w = true) := by
      ext w; simp [nbrV, randomGraph, edgeSetOf]
    rw [hn]
    rfl
  rw [← this]
  exact hcon

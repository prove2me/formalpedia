-- Prove2me | solution 1 for StrictCompatLB.RegularDegree.lemma_A_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:18:49.896345+00:00
-- url     : https://prove2.me/submissions/436a0dd9-d735-4fce-9b79-63218a2cf788

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

namespace StrictCompatLB.RegularDegree.RDInfra

open StrictCompatLB.MeanField StrictCompatLB.RegularDegree

lemma analytic_tail (N : ℕ) (hN : 1 ≤ N) (μ h : ℝ) (hh : 0 < h)
    (hμ : 6 / h * Real.log N ≤ μ) : μ * Real.exp (-(h * μ)) ≤ 2 / h * (1 / (N : ℝ) ^ 3) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hμ0 : 0 ≤ μ := le_trans (by positivity) hμ
  have h1 : h * μ / 2 ≤ Real.exp (h * μ / 2) := by
    have := Real.add_one_le_exp (h * μ / 2); linarith
  have h2 : μ ≤ 2 / h * Real.exp (h * μ / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hh]; linarith
  have h3 : Real.exp (-(h * μ / 2)) ≤ 1 / (N : ℝ) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    have : (N : ℝ) ^ 3 = Real.exp (3 * Real.log N) := by
      rw [show (3:ℝ) * Real.log N = ((3:ℕ):ℝ) * Real.log N by norm_num, Real.exp_nat_mul,
        Real.exp_log hNr]
    rw [this, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have : 6 * Real.log N ≤ h * μ := by
      have := mul_le_mul_of_nonneg_left hμ hh.le
      rw [← mul_assoc, mul_div_cancel₀ _ hh.ne'] at this; linarith
    linarith
  calc μ * Real.exp (-(h * μ)) ≤ (2 / h * Real.exp (h * μ / 2)) * Real.exp (-(h * μ)) := by
        gcongr
    _ = 2 / h * Real.exp (-(h * μ / 2)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 2 / h * (1 / (N : ℝ) ^ 3) := by gcongr

lemma ennreal_count {n C : ℕ} (N : ℕ) (hC : 0 < C) :
    (n : ENNReal) * (((C : ℕ) : ENNReal) ^ N)⁻¹ = ENNReal.ofReal ((n : ℝ) / (C : ℝ) ^ N) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow
    (by positivity), ENNReal.ofReal_natCast, div_eq_mul_inv]

end StrictCompatLB.RegularDegree.RDInfra

open StrictCompatLB.RegularDegree StrictCompatLB.MeanField StrictCompatLB.RegularDegree.RDInfra in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (hcM_log : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / ((M N : ℝ) * Real.log (N : ℝ)))
      atTop atTop) :
    ∀ᵐ ω ∂P, SatisfiesA19 M (randomGraph M adj ω) := by
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
  -- for each j, the bad events eventually do not occur
  have hj : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ N in atTop, ∀ v : Fin N,
      (lowNbr (adj N ω) ((1 - (1 / ((j:ℝ) + 1)) / 4) * ((N : ℝ) * c N / M N)) v : ℝ)
        ≤ (1 / ((j:ℝ) + 1)) * c N / (2 * ((N : ℝ) * c N / M N)) := by
    intro j
    set e : ℝ := 1 / ((j:ℝ) + 1) with he
    have he0 : 0 < e := by positivity
    have he1 : e ≤ 1 := by
      rw [he, div_le_one (by positivity)]; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
    let Bad : (N : ℕ) → Finset (Fin N → Fin (M N) → Bool) := fun N =>
      Finset.univ.filter (fun a => ∃ v, e * c N / (2 * ((N : ℝ) * c N / M N)) <
        (lowNbr a ((1 - e / 4) * ((N : ℝ) * c N / M N)) v : ℝ))
    set h : ℝ := (e / 4) ^ 2 / 4 with hh
    have hh0 : 0 < h := by positivity
    -- eventually μ ≥ (6/h) log N
    have hev : ∀ᶠ N : ℕ in atTop, 6 / h ≤ (N : ℝ) * (c N : ℝ) / ((M N : ℝ) * Real.log (N : ℝ)) :=
      hcM_log.eventually (eventually_ge_atTop _)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
    have hbound : ∀ N ≥ max N₁ 2, P (adj N ⁻¹' (Bad N : Set _))
        ≤ ENNReal.ofReal (2 / e * (2 / h) * (1 / (N : ℝ) ^ 2)) := by
      intro N hN
      have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
      have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
      have hk := hc_pos N
      have hkm := hcM N
      have hm : 1 ≤ M N := le_trans hk hkm
      have hNr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hmr : (0:ℝ) < M N := by exact_mod_cast hm
      have hkr : (0:ℝ) < c N := by exact_mod_cast hk
      set μ : ℝ := (N : ℝ) * c N / M N with hμ
      have hμ0 : 0 < μ := by positivity
      have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
      have hμlog : 6 / h * Real.log N ≤ μ := by
        have := hN₁ N hNN₁
        rw [le_div_iff₀ (by positivity)] at this
        rw [hμ]
        have e3 : (N : ℝ) * c N / M N = (N : ℝ) * c N / (M N * Real.log N) * Real.log N := by
          field_simp
        rw [e3]
        have := mul_le_mul_of_nonneg_right (hN₁ N hNN₁) hlog.le
        linarith
      rw [prob_eq P M c adj hadj N (Bad N)]
      have hfilt : (Bad N).filter (fun a => IsServerRegular (c N) a)
          = (Fintype.piFinset (fun _ : Fin N => rowSet (M N) (c N))).filter
              (fun a => ∃ v, e * c N / (2 * μ) < (lowNbr a ((1 - e / 4) * μ) v : ℝ)) := by
        rw [← reg_eq_piFinset, Finset.filter_filter, Finset.filter_filter]
        apply Finset.filter_congr
        intro a _
        exact and_comm
      rw [hfilt, ennreal_count N (Nat.choose_pos hkm)]
      apply ENNReal.ofReal_le_ofReal
      have hpb := prob_bound_A5 N (M N) (c N) (by omega) hk hkm (e * c N / (2 * μ)) (e / 4)
        (by positivity) (by positivity) (by linarith)
      refine hpb.trans ?_
      have e4 : (N : ℝ) / (e * c N / (2 * μ)) * c N = 2 / e * (N * μ) := by
        field_simp
      rw [e4]
      have hat := analytic_tail N (by omega) μ h hh0 hμlog
      have e5 : -(μ * (e / 4) ^ 2 / 4) = -(h * μ) := by rw [hh]; ring
      rw [e5]
      calc 2 / e * (↑N * μ) * Real.exp (-(h * μ))
          = 2 / e * N * (μ * Real.exp (-(h * μ))) := by ring
        _ ≤ 2 / e * N * (2 / h * (1 / (N : ℝ) ^ 3)) := by gcongr
        _ = 2 / e * (2 / h) * (1 / (N : ℝ) ^ 2) := by field_simp
    have hsum : Summable (fun N : ℕ => 2 / e * (2 / h) * (1 / (N : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _
    filter_upwards [ae_eventually_of_le P (fun N => adj N ⁻¹' (Bad N : Set _)) _ hsum _ hbound]
      with ω hω
    filter_upwards [hω] with N hN v
    by_contra hcon
    push_neg at hcon
    apply hN
    simp only [Set.mem_preimage, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      Bad]
    exact ⟨v, hcon⟩
  rw [← ae_all_iff] at hj
  filter_upwards [hreg, hj] with ω hreg hj
  intro ε hε
  obtain ⟨j, hjε⟩ := exists_nat_one_div_lt hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hj j)
  refine ⟨max N₀ 1, fun N hN v => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have he0 : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
  have he1 : 1 / ((j:ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
  have hdet := det_A5 N (M N) (c N) hN1 (hc_pos N) (hcM N) (adj N ω) (hreg N) _ he0 he1 v
    (hN₀ N hN0 v)
  have hrw : ∑ w : Fin (M N), (if (v, w) ∈ randomGraph M adj ω N then
      ((nbrW M (randomGraph M adj ω) N w).card : ℝ)⁻¹ else 0)
      = ∑ w, (if adj N ω v w = true then ((col (adj N ω) w : ℕ) : ℝ)⁻¹ else 0) := by
    apply Finset.sum_congr rfl
    intro w _
    simp [randomGraph, edgeSetOf, nbrW, col]
  rw [hrw]
  linarith

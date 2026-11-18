-- Prove2me | solution 1 for OWMR.renewal_concave_dfr
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:49.622891+00:00
-- url     : https://prove2.me/submissions/a6d74ab0-9dfb-4775-9a09-a4bb7ddd4737

import Definitions.Def_owmr_renewal
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Finset Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace BrownA

/-- Abel summation in inequality form: with `r` nondecreasing and nonnegative and all tails of
`Δ` beyond `l` nonnegative, `r l · ∑_{[l,N)} Δ ≤ ∑_{[l,N)} Δ_k r_k`. -/
lemma abel_ge (Δ r : ℕ → ℝ) (hr : Monotone r) (N : ℕ) :
    ∀ d l, N - l = d → (∀ l', l < l' → 0 ≤ ∑ k ∈ Ico l' N, Δ k) →
      r l * ∑ k ∈ Ico l N, Δ k ≤ ∑ k ∈ Ico l N, Δ k * r k := by
  intro d
  induction d with
  | zero =>
    intro l hl _
    have : N ≤ l := by omega
    simp [Finset.Ico_eq_empty_of_le this]
  | succ d ih =>
    intro l hl hT
    have hlN : l < N := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hlN, Finset.sum_eq_sum_Ico_succ_bot hlN]
    have h1 := ih (l + 1) (by omega) (fun l' hl' => hT l' (by omega))
    have h2 : 0 ≤ ∑ k ∈ Ico (l + 1) N, Δ k := hT (l + 1) (by omega)
    have h3 : r l ≤ r (l + 1) := hr (Nat.le_succ l)
    nlinarith [mul_le_mul_of_nonneg_right h3 h2]

/-- Discrete DFR renewal sequences are nonincreasing. Here `a k = ℙ(N > k)` for a positive
integer-valued step `N` with log-convex survival, and `v` is the renewal sequence
`v_0 = 1`, `v_{m+1} = ∑_{k ≤ m} ℙ(N = k+1) v_{m-k}`. -/
lemma disc_antitone (a v : ℕ → ℝ) (ha0 : a 0 = 1) (hapos : ∀ k, 0 < a k)
    (hmono : ∀ k, a (k + 1) ≤ a k) (hlc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2))
    (hv0 : v 0 = 1)
    (hv : ∀ m, v (m + 1) = ∑ k ∈ range (m + 1), (a k - a (k + 1)) * v (m - k)) :
    ∀ m, v (m + 1) ≤ v m := by
  have hvnn : ∀ m, 0 ≤ v m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      cases m with
      | zero => rw [hv0]; norm_num
      | succ m =>
        rw [hv m]
        exact Finset.sum_nonneg fun k hk => mul_nonneg (sub_nonneg.2 (hmono k))
          (ih _ (by have := Finset.mem_range.1 hk; omega))
  set π : ℕ → ℕ → ℝ := fun m k => v (m - k) * a k with hπ
  have hπnn : ∀ m k, 0 ≤ π m k := fun m k => mul_nonneg (hvnn _) (hapos k).le
  have hmass : ∀ m, ∑ k ∈ range (m + 1), π m k = 1 := by
    intro m
    induction m with
    | zero => simp [hπ, hv0, ha0]
    | succ m ih =>
      rw [Finset.sum_range_succ']
      have e1 : ∀ k ∈ range (m + 1), π (m + 1) (k + 1) = v (m - k) * a (k + 1) := by
        intro k _
        simp only [hπ, Nat.add_sub_add_right]
      rw [Finset.sum_congr rfl e1]
      have e0 : π (m + 1) 0 = v (m + 1) := by simp [hπ, ha0]
      rw [e0, hv m, ← ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hπ]
      ring
  set T : ℕ → ℕ → ℝ := fun m j => ∑ k ∈ Ico j (m + 1), π m k with hT
  have hsplit : ∀ m, π m 0 + T m 1 = 1 := by
    intro m
    rw [← hmass m, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos m)]
  set r : ℕ → ℝ := fun k => a (k + 1) / a k with hr
  have hrmono : Monotone r := by
    refine monotone_nat_of_le_succ fun k => ?_
    simp only [hr]
    rw [div_le_div_iff₀ (hapos k) (hapos (k + 1))]
    nlinarith [hlc k]
  have hr0 : ∀ k, 0 ≤ r k := fun k => div_nonneg (hapos _).le (hapos _).le
  have hshift : ∀ m i, T (m + 1) (i + 1) = ∑ k ∈ Ico i (m + 1), π m k * r k := by
    intro m i
    simp only [hT]
    rw [show m + 1 + 1 = (m + 1) + 1 from rfl, ← Finset.sum_Ico_add' (c := 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hπ, hr, Nat.add_sub_add_right]
    field_simp [(hapos k).ne']
  have hT0 : ∀ m j, 0 ≤ T m j := fun m j => Finset.sum_nonneg fun k _ => hπnn m k
  have hTtop : ∀ m, T m (m + 1) = 0 := fun m => by simp [hT]
  -- main induction: tails increase in `m`
  have hmain : ∀ m j, 1 ≤ j → T m j ≤ T (m + 1) j := by
    intro m
    induction m with
    | zero =>
      intro j hj
      have : T 0 j = 0 := by
        simp only [hT]
        exact Finset.sum_eq_zero fun k hk => by
          have := Finset.mem_Ico.1 hk; omega
      rw [this]; exact hT0 _ _
    | succ m ih =>
      intro j hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      set Δ : ℕ → ℝ := fun k => π (m + 1) k - (if k < m + 1 then π m k else 0) with hΔ
      -- tails of `Δ`
      have htail : ∀ l, ∑ k ∈ Ico l (m + 2), Δ k = T (m + 1) l - T m l := by
        intro l
        simp only [hΔ, hT, Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      have htail_nn : ∀ l, 0 ≤ ∑ k ∈ Ico l (m + 2), Δ k := by
        intro l
        rw [htail]
        rcases Nat.eq_zero_or_pos l with hl | hl
        · subst hl
          have h1 := hsplit (m + 1)
          have h2 := hsplit m
          have e1 : T (m + 1) 0 = π (m + 1) 0 + T (m + 1) 1 := by
            simp only [hT]
            rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
          have e2 : T m 0 = π m 0 + T m 1 := by
            simp only [hT]
            rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
          linarith
        · linarith [ih l hl]
      have hdiff : T (m + 1 + 1) (i + 1) - T (m + 1) (i + 1)
          = ∑ k ∈ Ico i (m + 2), Δ k * r k := by
        rw [hshift (m + 1) i, hshift m i]
        simp only [hΔ, sub_mul, Finset.sum_sub_distrib]
        congr 1
        simp only [ite_mul, zero_mul]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      have habel := abel_ge Δ r hrmono (m + 2) _ i rfl (fun l' _ => htail_nn l')
      have := mul_nonneg (hr0 i) (htail_nn i)
      linarith
  intro m
  have h1 := hsplit (m + 1)
  have h2 := hsplit m
  have e1 : π (m + 1) 0 = v (m + 1) := by simp [hπ, ha0]
  have e2 : π m 0 = v m := by simp [hπ, ha0]
  have h3 := hmain m 1 le_rfl
  linarith

end BrownA

namespace BrownB

variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

/-- Rounding index `⌈z/δ⌉`. -/
def cl (δ : ℝ) (z : ℝ≥0) : ℕ := ⌈(z : ℝ) / δ⌉₊

lemma measurable_cl (δ : ℝ) : Measurable (cl δ) :=
  Nat.measurable_ceil.comp (measurable_subtype_coe.div_const δ)

lemma measurable_sumcl (δ : ℝ) (n : ℕ) :
    Measurable (fun z : Fin n → ℝ≥0 => ∑ j, cl δ (z j)) :=
  Finset.measurable_sum _ fun j _ => (measurable_cl δ).comp (measurable_pi_apply j)

/-- `ℙ(∑_{j<n} ⌈D_j/δ⌉ = k)`. -/
def Pn (δ : ℝ) (n k : ℕ) : ℝ≥0∞ := (Measure.pi fun _ : Fin n => ρ) {z | ∑ j, cl δ (z j) = k}

/-- Discretized renewal mass at the lattice point `k δ`. -/
def uu (δ : ℝ) (k : ℕ) : ℝ≥0∞ := ∑' n, Pn ρ δ n k

/-- `ℙ(⌈D/δ⌉ = j)`. -/
def piv (δ : ℝ) (j : ℕ) : ℝ≥0∞ := ρ {z | cl δ z = j}

lemma Pn_zero (δ : ℝ) (k : ℕ) : Pn ρ δ 0 k = if k = 0 then 1 else 0 := by
  unfold Pn
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    have : {z : Fin 0 → ℝ≥0 | ∑ j, cl δ (z j) = k} = ∅ := by
      ext z
      simp only [Finset.univ_eq_empty, Finset.sum_empty, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false]
      exact fun h => hk h.symm
    rw [this, measure_empty]

lemma Pn_succ (δ : ℝ) (n k : ℕ) :
    Pn ρ δ (n + 1) k = ∑ j ∈ range (k + 1), piv ρ δ j * Pn ρ δ n (k - j) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ρ) 0
  set A : Set (ℝ≥0 × (Fin n → ℝ≥0)) := {p | cl δ p.1 + ∑ j, cl δ (p.2 j) = k} with hA
  have hAm : MeasurableSet A :=
    measurableSet_eq_fun ((measurable_cl δ).comp measurable_fst |>.add
      ((measurable_sumcl δ n).comp measurable_snd)) measurable_const
  have hpre : {z : Fin (n + 1) → ℝ≥0 | ∑ j, cl δ (z j) = k}
      = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ≥0) 0 ⁻¹' A := by
    ext z
    simp [hA, Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
  unfold Pn
  rw [hpre, hmp.measure_preimage hAm.nullMeasurableSet, Measure.prod_apply hAm]
  have hsec : ∀ y : ℝ≥0, (Measure.pi fun _ : Fin n => ρ) (Prod.mk y ⁻¹' A)
      = if cl δ y ≤ k then Pn ρ δ n (k - cl δ y) else 0 := by
    intro y
    unfold Pn
    split_ifs with hy
    · congr 1
      ext z
      simp only [hA, Set.mem_preimage, Set.mem_setOf_eq]
      omega
    · have : Prod.mk y ⁻¹' A = ∅ := by
        ext z
        simp only [hA, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        omega
      rw [this, measure_empty]
  simp_rw [hsec]
  set G : ℕ → ℝ≥0∞ := fun j => if j ≤ k then Pn ρ δ n (k - j) else 0 with hG
  have hGc : (fun y : ℝ≥0 => if cl δ y ≤ k then Pn ρ δ n (k - cl δ y) else 0)
      = G ∘ cl δ := rfl
  have hmap := lintegral_map (μ := ρ) (measurable_of_countable G) (measurable_cl δ)
  rw [hGc, show lintegral ρ (G ∘ cl δ) = ∫⁻ a, G (cl δ a) ∂ρ from rfl, ← hmap,
    lintegral_countable']
  rw [tsum_eq_sum (s := range (k + 1))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [Measure.map_apply (measurable_cl δ) (measurableSet_singleton j)]
    simp only [hG, if_pos hjk, piv]
    rw [mul_comm]
    rfl
  · intro j hj
    have : ¬ j ≤ k := fun h => hj (Finset.mem_range.2 (Nat.lt_succ_of_le h))
    simp [hG, this]

lemma uu_rec (δ : ℝ) (k : ℕ) :
    uu ρ δ k = (if k = 0 then 1 else 0) + ∑ j ∈ range (k + 1), piv ρ δ j * uu ρ δ (k - j) := by
  unfold uu
  rw [tsum_eq_zero_add' ENNReal.summable, Pn_zero]
  congr 1
  simp_rw [Pn_succ]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.tsum_mul_left]

/-- `renewalM` as the renewal measure of `[0, w)`. -/
lemma renewalM_eq (w : ℝ) : OWMR.renewalM ρ w = OWMR.renewalMeasure ρ (Set.Ico 0 w) := by
  unfold OWMR.renewalM OWMR.renewalMeasure
  rw [Measure.sum_apply _ measurableSet_Ico]
  refine tsum_congr fun k => ?_
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ico]
  constructor
  · intro h; exact ⟨Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _, h⟩
  · exact fun h => h.2

lemma cl_ge (δ : ℝ) (hδ : 0 < δ) (z : ℝ≥0) : (z : ℝ) ≤ δ * cl δ z := by
  unfold cl
  have := Nat.le_ceil ((z : ℝ) / δ)
  rw [div_le_iff₀ hδ] at this
  linarith

lemma cl_lt (δ : ℝ) (hδ : 0 < δ) (z : ℝ≥0) : δ * cl δ z < (z : ℝ) + δ := by
  unfold cl
  have := Nat.ceil_lt_add_one (div_nonneg z.2 hδ.le)
  have h2 : δ * (⌈(z : ℝ) / δ⌉₊ : ℝ) < δ * ((z : ℝ) / δ + 1) := mul_lt_mul_of_pos_left this hδ
  rw [mul_add, mul_div_cancel₀ _ hδ.ne', mul_one] at h2
  exact h2

lemma uu_lt_top (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    uu ρ δ k < ∞ := by
  refine lt_of_le_of_lt ?_ (OWMR.renewalMeasure_Ico_lt_top ρ hρ ((k + 1) * δ))
  rw [← renewalM_eq]
  unfold uu OWMR.renewalM
  refine ENNReal.tsum_le_tsum fun n => measure_mono ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz ⊢
  have : ∑ j, (z j : ℝ) ≤ δ * (k : ℝ) := by
    calc ∑ j, (z j : ℝ) ≤ ∑ j, δ * (cl δ (z j) : ℝ) :=
          Finset.sum_le_sum fun j _ => cl_ge δ hδ (z j)
      _ = δ * (k : ℝ) := by rw [← Finset.mul_sum]; exact_mod_cast congrArg (fun m : ℕ => δ * (m : ℝ)) hz
  nlinarith

/-! ### Part C: survival function and the real recursion -/

/-- Survival function `ℙ(D > x)`. -/
def sv (x : ℝ) : ℝ := (ρ {z : ℝ≥0 | x < (z : ℝ)}).toReal

lemma sv_anti {x y : ℝ} (hxy : x ≤ y) : sv ρ y ≤ sv ρ x := by
  unfold sv
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  intro z hz
  simp only [Set.mem_setOf_eq] at hz ⊢
  linarith

lemma sv_nonneg (x : ℝ) : 0 ≤ sv ρ x := ENNReal.toReal_nonneg

lemma sv_le_one (x : ℝ) : sv ρ x ≤ 1 := by
  unfold sv
  have := prob_le_one (μ := ρ) (s := {z : ℝ≥0 | x < (z : ℝ)})
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

lemma piv_zero_real (δ : ℝ) (hδ : 0 < δ) : (piv ρ δ 0).toReal = 1 - sv ρ 0 := by
  have hset : {z : ℝ≥0 | cl δ z = 0} = {z : ℝ≥0 | (0 : ℝ) < (z : ℝ)}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt, cl, Nat.ceil_eq_zero]
    rw [div_le_iff₀ hδ, zero_mul]
  have hm : MeasurableSet {z : ℝ≥0 | (0 : ℝ) < (z : ℝ)} :=
    measurableSet_lt measurable_const measurable_coe_nnreal_real
  unfold piv sv
  rw [hset, prob_compl_eq_one_sub hm,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

lemma piv_succ_real (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    (piv ρ δ (j + 1)).toReal = sv ρ (j * δ) - sv ρ ((j + 1) * δ) := by
  have hsub : {z : ℝ≥0 | ((j : ℝ) + 1) * δ < (z : ℝ)} ⊆ {z : ℝ≥0 | (j : ℝ) * δ < (z : ℝ)} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    nlinarith
  have hset : {z : ℝ≥0 | cl δ z = j + 1}
      = {z : ℝ≥0 | (j : ℝ) * δ < (z : ℝ)} \ {z : ℝ≥0 | ((j : ℝ) + 1) * δ < (z : ℝ)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt, cl]
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero j)]
    push_cast
    rw [lt_div_iff₀ hδ, div_le_iff₀ hδ]
  have hm : MeasurableSet {z : ℝ≥0 | ((j : ℝ) + 1) * δ < (z : ℝ)} :=
    measurableSet_lt measurable_const measurable_coe_nnreal_real
  unfold piv sv
  rw [hset, measure_diff hsub hm.nullMeasurableSet (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top _ _)]

lemma uu_rec_real (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    (uu ρ δ k).toReal = (if k = 0 then 1 else 0)
      + ∑ j ∈ range (k + 1), (piv ρ δ j).toReal * (uu ρ δ (k - j)).toReal := by
  have hfin : ∀ i, uu ρ δ i ≠ ∞ := fun i => (uu_lt_top ρ hρ δ hδ i).ne
  have hpfin : ∀ j, piv ρ δ j ≠ ∞ := fun j => measure_ne_top _ _
  conv_lhs => rw [uu_rec]
  rw [ENNReal.toReal_add (by split_ifs <;> simp)
    (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top (hpfin j) (hfin _)),
    ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top (hpfin j) (hfin _))]
  congr 1
  · split_ifs <;> simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.toReal_mul]

/-! ### Part H: positivity of the survival function -/

lemma sv_pos (hq : 0 < sv ρ 0)
    (hlc : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      sv ρ (η * x + (1 - η) * y) ≤ sv ρ x ^ η * sv ρ y ^ (1 - η)) :
    ∀ x : ℝ, 0 ≤ x → 0 < sv ρ x := by
  intro x hx
  by_contra hneg
  have hx0 : sv ρ x = 0 := le_antisymm (not_lt.1 hneg) (sv_nonneg ρ x)
  have hxpos : 0 < x := by
    rcases hx.lt_or_eq with h | h
    · exact h
    · subst h; linarith
  have hzero : ∀ y, 0 < y → y < x → sv ρ y = 0 := by
    intro y hy hyx
    have hη0 : 0 ≤ 1 - y / x := by rw [sub_nonneg, div_le_one hxpos]; linarith
    have hη1 : 1 - y / x ≤ 1 := by have := div_pos hy hxpos; linarith
    have h := hlc 0 x (1 - y / x) le_rfl hx hη0 hη1
    have e : (1 - y / x) * 0 + (1 - (1 - y / x)) * x = y := by field_simp; ring
    have hne : (1 - (1 - y / x)) ≠ 0 := by have := div_pos hy hxpos; intro h'; linarith
    rw [e, hx0, Real.zero_rpow hne, mul_zero] at h
    exact le_antisymm h (sv_nonneg ρ y)
  have hnull : ∀ y, 0 < y → y < x → ρ {z : ℝ≥0 | y < (z : ℝ)} = 0 := by
    intro y hy hyx
    have := hzero y hy hyx
    unfold sv at this
    rcases (ENNReal.toReal_eq_zero_iff _).1 this with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have hU : {z : ℝ≥0 | (0 : ℝ) < (z : ℝ)} ⊆ ⋃ n : ℕ, {z : ℝ≥0 | x / (n + 2) < (z : ℝ)} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    obtain ⟨n, hn⟩ := exists_nat_gt (x / (z : ℝ))
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hz] at hn
    nlinarith
  have h0 : ρ {z : ℝ≥0 | (0 : ℝ) < (z : ℝ)} = 0 := by
    refine measure_mono_null hU (measure_iUnion_null fun n => hnull _ (by positivity) ?_)
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have : sv ρ 0 = 0 := by unfold sv; rw [h0]; rfl
  linarith

/-! ### Part C2: the discretized renewal masses are nonincreasing -/

lemma uhat_antitone (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (hq : 0 < sv ρ 0)
    (hlc : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      sv ρ (η * x + (1 - η) * y) ≤ sv ρ x ^ η * sv ρ y ^ (1 - η))
    (δ : ℝ) (hδ : 0 < δ) : ∀ k, (uu ρ δ (k + 1)).toReal ≤ (uu ρ δ k).toReal := by
  set q := sv ρ 0 with hqdef
  set a : ℕ → ℝ := fun k => sv ρ (k * δ) / q with ha
  set w : ℕ → ℝ := fun k => q * (uu ρ δ k).toReal with hw
  have hpos := sv_pos ρ hq hlc
  have ha0 : a 0 = 1 := by
    show sv ρ (((0 : ℕ) : ℝ) * δ) / q = 1
    rw [Nat.cast_zero, zero_mul, ← hqdef]
    exact div_self hq.ne'
  have hapos : ∀ k, 0 < a k := fun k => div_pos (hpos _ (by positivity)) hq
  have hmono : ∀ k, a (k + 1) ≤ a k := by
    intro k
    simp only [ha]
    refine div_le_div_of_nonneg_right (sv_anti ρ ?_) hq.le
    push_cast
    nlinarith
  have hlca : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2) := by
    intro k
    have h := hlc (k * δ) ((k + 2) * δ) (1 / 2) (by positivity) (by positivity) (by norm_num)
      (by norm_num)
    have e : (1 / 2 : ℝ) * (k * δ) + (1 - 1 / 2) * ((k + 2) * δ) = ((k + 1 : ℕ) : ℝ) * δ := by
      push_cast; ring
    rw [e] at h
    have e2 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [e2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
    have hs1 := Real.sq_sqrt (sv_nonneg ρ (k * δ))
    have hs2 := Real.sq_sqrt (sv_nonneg ρ ((k + 2) * δ))
    have hl : 0 ≤ sv ρ (((k + 1 : ℕ) : ℝ) * δ) := sv_nonneg ρ _
    have hsq : sv ρ (((k + 1 : ℕ) : ℝ) * δ) ^ 2 ≤ sv ρ (k * δ) * sv ρ ((k + 2) * δ) := by
      have := pow_le_pow_left₀ hl h 2
      rw [mul_pow, hs1, hs2] at this
      exact this
    simp only [ha]
    rw [div_pow, div_mul_div_comm, ← sq]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have e3 : ((k + 2 : ℕ) : ℝ) * δ = ((k : ℝ) + 2) * δ := by push_cast; ring
    rw [e3]
    exact hsq
  have hrec := uu_rec_real ρ hρ δ hδ
  have hp0 := piv_zero_real ρ δ hδ
  have hw0 : w 0 = 1 := by
    have h := hrec 0
    rw [if_pos rfl, zero_add, Finset.sum_range_one, Nat.sub_self, hp0] at h
    simp only [hw]
    rw [← hqdef] at h
    nlinarith
  have hwrec : ∀ m, w (m + 1) = ∑ k ∈ range (m + 1), (a k - a (k + 1)) * w (m - k) := by
    intro m
    have h := hrec (m + 1)
    rw [if_neg (Nat.succ_ne_zero m), zero_add, Finset.sum_range_succ'] at h
    simp only [Nat.sub_zero, Nat.add_sub_add_right] at h
    rw [hp0, ← hqdef] at h
    have hsum : ∑ j ∈ range (m + 1), (piv ρ δ (j + 1)).toReal * (uu ρ δ (m - j)).toReal
        = ∑ k ∈ range (m + 1), (a k - a (k + 1)) * w (m - k) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [piv_succ_real ρ δ hδ j]
      simp only [ha, hw]
      push_cast
      field_simp
    simp only [hw]
    rw [← hsum]
    linarith
  have hw_anti := BrownA.disc_antitone a w ha0 hapos hmono hlca hw0 hwrec
  intro k
  have := hw_anti k
  simp only [hw] at this
  exact le_of_mul_le_mul_left this hq

/-! ### Part D: lattice sums and the dyadic limit -/

/-- `R_δ(x) = ∑_n ℙ(δ ∑_{j<n} ⌈D_j/δ⌉ < x)`. -/
def Rf (δ x : ℝ) : ℝ≥0∞ :=
  ∑' n, (Measure.pi fun _ : Fin n => ρ) {z | δ * ((∑ j, cl δ (z j) : ℕ) : ℝ) < x}

lemma Rf_lattice (δ : ℝ) (hδ : 0 < δ) (m : ℕ) :
    Rf ρ δ (m * δ) = ∑ k ∈ range m, uu ρ δ k := by
  unfold Rf uu
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun n => ?_
  have hset : {z : Fin n → ℝ≥0 | δ * ((∑ j, cl δ (z j) : ℕ) : ℝ) < m * δ}
      = ⋃ k ∈ range m, {z | ∑ j, cl δ (z j) = k} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    rw [mul_comm δ, mul_lt_mul_iff_left₀ hδ, Nat.cast_lt]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨k, hk, hz⟩; rw [hz]; exact hk
  rw [hset, measure_biUnion_finset]
  · rfl
  · intro k _ k' _ hkk'
    exact Set.disjoint_left.2 fun z h1 h2 => hkk' (h1.symm.trans h2)
  · intro k _
    exact measurableSet_eq_fun (measurable_sumcl δ n) measurable_const

/-- Dyadic mesh `2^{-N}`. -/
def dy (N : ℕ) : ℝ := 1 / 2 ^ N

lemma dy_pos (N : ℕ) : 0 < dy N := by unfold dy; positivity

lemma dy_succ (N : ℕ) : dy (N + 1) = dy N / 2 := by unfold dy; rw [pow_succ]; field_simp

lemma cl_dy (N : ℕ) (z : ℝ≥0) : cl (dy N) z = ⌈(z : ℝ) * 2 ^ N⌉₊ := by
  unfold cl dy
  rw [div_div_eq_mul_div, div_one]

lemma cl_dy_mono (N : ℕ) (z : ℝ≥0) :
    dy (N + 1) * (cl (dy (N + 1)) z : ℝ) ≤ dy N * (cl (dy N) z : ℝ) := by
  rw [cl_dy, cl_dy, dy_succ]
  have h1 : ⌈(z : ℝ) * 2 ^ (N + 1)⌉₊ ≤ 2 * ⌈(z : ℝ) * 2 ^ N⌉₊ := by
    rw [Nat.ceil_le]
    push_cast
    rw [pow_succ]
    have := Nat.le_ceil ((z : ℝ) * 2 ^ N)
    nlinarith
  have h2 : ((⌈(z : ℝ) * 2 ^ (N + 1)⌉₊ : ℕ) : ℝ) ≤ 2 * (⌈(z : ℝ) * 2 ^ N⌉₊ : ℝ) := by
    exact_mod_cast h1
  have := dy_pos N
  nlinarith

lemma tsum_iSup_mono (f : ℕ → ℕ → ℝ≥0∞) (hf : Monotone f) :
    ∑' n, ⨆ N, f N n = ⨆ N, ∑' n, f N n := by
  have h := lintegral_iSup (μ := Measure.count) (f := f) (fun N => measurable_of_countable _) hf
  simp only [lintegral_count] at h
  rw [← h]

lemma renewalM_iSup (x : ℝ) : OWMR.renewalM ρ x = ⨆ N, Rf ρ (dy N) x := by
  set A : ℕ → (n : ℕ) → Set (Fin n → ℝ≥0) :=
    fun N n => {z | dy N * ((∑ j, cl (dy N) (z j) : ℕ) : ℝ) < x} with hA
  have hmono : ∀ n, Monotone fun N => A N n := by
    intro n
    refine monotone_nat_of_le_succ fun N z hz => ?_
    simp only [hA, Set.mem_setOf_eq] at hz ⊢
    refine lt_of_le_of_lt ?_ hz
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => cl_dy_mono N (z j)
  have hunion : ∀ n, ⋃ N, A N n = {z : Fin n → ℝ≥0 | ∑ j, (z j : ℝ) < x} := by
    intro n
    ext z
    simp only [hA, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨N, hN⟩
      refine lt_of_le_of_lt ?_ hN
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => cl_ge (dy N) (dy_pos N) (z j)
    · intro hz
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0
        refine ⟨0, ?_⟩
        simpa using hz
      have hgap : 0 < x - ∑ j, (z j : ℝ) := by linarith
      obtain ⟨N, hN⟩ : ∃ N : ℕ, (n : ℝ) * dy N < x - ∑ j, (z j : ℝ) := by
        have ht : Tendsto (fun N : ℕ => (n : ℝ) * dy N) atTop (𝓝 0) := by
          have : Tendsto (fun N : ℕ => dy N) atTop (𝓝 0) := by
            unfold dy
            simp only [one_div, ← inv_pow]
            exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
          simpa using this.const_mul (n : ℝ)
        exact (ht.eventually (gt_mem_nhds hgap)).exists
      refine ⟨N, ?_⟩
      push_cast
      rw [Finset.mul_sum]
      calc ∑ j, dy N * (cl (dy N) (z j) : ℝ) < ∑ j : Fin n, ((z j : ℝ) + dy N) :=
            Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hn0⟩⟩)
                fun j _ => cl_lt (dy N) (dy_pos N) (z j)
        _ = ∑ j, (z j : ℝ) + n * dy N := by
            rw [Finset.sum_add_distrib]; simp
        _ < x := by linarith
  unfold OWMR.renewalM Rf
  have : ∀ n, (Measure.pi fun _ : Fin n => ρ) {z : Fin n → ℝ≥0 | ∑ j, (z j : ℝ) < x}
      = ⨆ N, (Measure.pi fun _ : Fin n => ρ) (A N n) := by
    intro n
    rw [← hunion n, (hmono n).measure_iUnion]
  simp_rw [this]
  exact tsum_iSup_mono (fun N n => (Measure.pi fun _ : Fin n => ρ) (A N n))
    (fun N N' h n => measure_mono (hmono n h))

lemma renewalM_lt_top (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (x : ℝ) : OWMR.renewalM ρ x < ∞ := by
  rw [renewalM_eq]; exact OWMR.renewalMeasure_Ico_lt_top ρ hρ x

lemma Rf_tendsto (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (x : ℝ) :
    Tendsto (fun N => (Rf ρ (dy N) x).toReal) atTop (𝓝 (OWMR.renewalM ρ x).toReal) := by
  have hmono : Monotone fun N => Rf ρ (dy N) x := by
    have h := renewalM_iSup ρ x
    -- monotonicity directly from set inclusions
    refine monotone_nat_of_le_succ fun N => ENNReal.tsum_le_tsum fun n => measure_mono ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    refine lt_of_le_of_lt ?_ hz
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => cl_dy_mono N (z j)
  have h1 := tendsto_atTop_iSup hmono
  rw [← renewalM_iSup] at h1
  exact (ENNReal.tendsto_toReal (renewalM_lt_top ρ hρ x).ne).comp h1

/-! ### Part E: nonincreasing increments of `M` at dyadic points -/

lemma lattice_incr (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (hq : 0 < sv ρ 0)
    (hlc : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      sv ρ (η * x + (1 - η) * y) ≤ sv ρ x ^ η * sv ρ y ^ (1 - η))
    (N m m' l : ℕ) (hmm : m ≤ m') :
    (Rf ρ (dy N) (((m' + l : ℕ) : ℝ) * dy N)).toReal - (Rf ρ (dy N) ((m' : ℝ) * dy N)).toReal
      ≤ (Rf ρ (dy N) (((m + l : ℕ) : ℝ) * dy N)).toReal - (Rf ρ (dy N) ((m : ℝ) * dy N)).toReal := by
  have hfin : ∀ k, uu ρ (dy N) k ≠ ∞ := fun k => (uu_lt_top ρ hρ (dy N) (dy_pos N) k).ne
  have hanti : Antitone fun k => (uu ρ (dy N) k).toReal :=
    antitone_nat_of_succ_le (uhat_antitone ρ hρ hq hlc (dy N) (dy_pos N))
  have hR : ∀ k : ℕ, (Rf ρ (dy N) ((k : ℝ) * dy N)).toReal
      = ∑ i ∈ range k, (uu ρ (dy N) i).toReal := by
    intro k
    rw [Rf_lattice ρ (dy N) (dy_pos N) k, ENNReal.toReal_sum fun i _ => hfin i]
  rw [hR, hR, hR, hR, Finset.sum_range_add, Finset.sum_range_add]
  simp only [add_sub_cancel_left]
  exact Finset.sum_le_sum fun i _ => hanti (by omega)

lemma dy_scale (N0 N : ℕ) (h : N0 ≤ N) (m : ℕ) :
    ((m * 2 ^ (N - N0) : ℕ) : ℝ) * dy N = (m : ℝ) * dy N0 := by
  unfold dy
  have : (2 : ℝ) ^ N = 2 ^ (N - N0) * 2 ^ N0 := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [this]
  push_cast
  field_simp

lemma dyadic_incr (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (hq : 0 < sv ρ 0)
    (hlc : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      sv ρ (η * x + (1 - η) * y) ≤ sv ρ x ^ η * sv ρ y ^ (1 - η))
    (N0 m m' l : ℕ) (hmm : m ≤ m') :
    (OWMR.renewalM ρ (((m' + l : ℕ) : ℝ) * dy N0)).toReal
        - (OWMR.renewalM ρ ((m' : ℝ) * dy N0)).toReal
      ≤ (OWMR.renewalM ρ (((m + l : ℕ) : ℝ) * dy N0)).toReal
        - (OWMR.renewalM ρ ((m : ℝ) * dy N0)).toReal := by
  have hev : ∀ᶠ N in atTop,
      (Rf ρ (dy N) (((m' + l : ℕ) : ℝ) * dy N0)).toReal - (Rf ρ (dy N) ((m' : ℝ) * dy N0)).toReal
        ≤ (Rf ρ (dy N) (((m + l : ℕ) : ℝ) * dy N0)).toReal
          - (Rf ρ (dy N) ((m : ℝ) * dy N0)).toReal := by
    filter_upwards [eventually_ge_atTop N0] with N hN
    have h := lattice_incr ρ hρ hq hlc N (m * 2 ^ (N - N0)) (m' * 2 ^ (N - N0))
      (l * 2 ^ (N - N0)) (Nat.mul_le_mul_right _ hmm)
    rw [show m' * 2 ^ (N - N0) + l * 2 ^ (N - N0) = (m' + l) * 2 ^ (N - N0) by ring,
      show m * 2 ^ (N - N0) + l * 2 ^ (N - N0) = (m + l) * 2 ^ (N - N0) by ring,
      dy_scale N0 N hN, dy_scale N0 N hN, dy_scale N0 N hN, dy_scale N0 N hN] at h
    exact h
  exact le_of_tendsto_of_tendsto (((Rf_tendsto ρ hρ _).sub (Rf_tendsto ρ hρ _)))
    ((Rf_tendsto ρ hρ _).sub (Rf_tendsto ρ hρ _)) hev

/-! ### Part F: nonincreasing increments of `x ↦ U[0,x]` -/

/-- `U[0, x]` as a real number. -/
def Wf (x : ℝ) : ℝ := (OWMR.renewalMeasure ρ (Set.Icc 0 x)).toReal

lemma V_to_W (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (s : ℕ → ℝ) (r : ℝ) (hs : Antitone s)
    (hrs : ∀ n, r < s n) (hlim : Tendsto s atTop (𝓝 r)) :
    Tendsto (fun n => (OWMR.renewalM ρ (s n)).toReal) atTop (𝓝 (Wf ρ r)) := by
  simp_rw [renewalM_eq]
  have hanti : Antitone fun n => Set.Ico (0 : ℝ) (s n) :=
    fun a b hab => Set.Ico_subset_Ico_right (hs hab)
  have hinter : ⋂ n, Set.Ico (0 : ℝ) (s n) = Set.Icc 0 r := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Ico, Set.mem_Icc]
    constructor
    · intro h
      refine ⟨(h 0).1, ?_⟩
      exact ge_of_tendsto hlim (Eventually.of_forall fun n => (h n).2.le)
    · rintro ⟨h0, hr⟩ n
      exact ⟨h0, lt_of_le_of_lt hr (hrs n)⟩
  have h := tendsto_measure_iInter_atTop (μ := OWMR.renewalMeasure ρ)
    (fun n => measurableSet_Ico.nullMeasurableSet) hanti
    ⟨0, (OWMR.renewalMeasure_Ico_lt_top ρ hρ (s 0)).ne⟩
  rw [hinter] at h
  have hfinW : OWMR.renewalMeasure ρ (Set.Icc 0 r) ≠ ∞ :=
    ne_top_of_le_ne_top (OWMR.renewalMeasure_Ico_lt_top ρ hρ (s 0)).ne
      (measure_mono (Set.Icc_subset_Ico_right (hrs 0)))
  exact (ENNReal.tendsto_toReal hfinW).comp h

/-- Dyadic approximation from above. -/
def ap (n : ℕ) (r : ℝ) : ℝ := ((⌊r * 2 ^ n⌋₊ + 1 : ℕ) : ℝ) * dy n

lemma ap_gt (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : r < ap n r := by
  unfold ap dy
  have h := Nat.lt_floor_add_one (r * 2 ^ n)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [mul_one_div, lt_div_iff₀ h2]
  push_cast
  exact h

lemma ap_le (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : ap n r ≤ r + dy n := by
  unfold ap dy
  have h := Nat.floor_le (mul_nonneg hr (by positivity : (0 : ℝ) ≤ 2 ^ n))
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [mul_one_div, div_le_iff₀ h2, add_mul, one_div_mul_cancel h2.ne']
  push_cast
  linarith

lemma ap_anti {r : ℝ} (hr : 0 ≤ r) : Antitone fun n => ap n r := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold ap
  rw [dy_succ]
  have ht : 0 ≤ r * 2 ^ n := mul_nonneg hr (by positivity)
  have h1 : ⌊r * 2 ^ (n + 1)⌋₊ ≤ 2 * ⌊r * 2 ^ n⌋₊ + 1 := by
    have : ⌊r * 2 ^ (n + 1)⌋₊ < 2 * ⌊r * 2 ^ n⌋₊ + 2 := by
      rw [Nat.floor_lt (mul_nonneg hr (by positivity))]
      push_cast
      rw [pow_succ]
      have := Nat.lt_floor_add_one (r * 2 ^ n)
      nlinarith
    omega
  have h2 : ((⌊r * 2 ^ (n + 1)⌋₊ : ℕ) : ℝ) ≤ 2 * (⌊r * 2 ^ n⌋₊ : ℝ) + 1 := by exact_mod_cast h1
  have := dy_pos n
  push_cast
  nlinarith

lemma ap_tendsto {r : ℝ} (hr : 0 ≤ r) : Tendsto (fun n => ap n r) atTop (𝓝 r) := by
  have hdy : Tendsto (fun N : ℕ => dy N) atTop (𝓝 0) := by
    unfold dy
    simp only [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hup : Tendsto (fun n => r + dy n) atTop (𝓝 r) := by simpa using hdy.const_add r
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (ap_gt n hr).le) (fun n => ap_le n hr)

lemma W_incr (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (hq : 0 < sv ρ 0)
    (hlc : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      sv ρ (η * x + (1 - η) * y) ≤ sv ρ x ^ η * sv ρ y ^ (1 - η))
    (x y h : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hh : 0 ≤ h) :
    Wf ρ (y + h) - Wf ρ y ≤ Wf ρ (x + h) - Wf ρ x := by
  have hy : 0 ≤ y := hx.trans hxy
  have key : ∀ n, (OWMR.renewalM ρ (ap n y + ap n h)).toReal - (OWMR.renewalM ρ (ap n y)).toReal
      ≤ (OWMR.renewalM ρ (ap n x + ap n h)).toReal - (OWMR.renewalM ρ (ap n x)).toReal := by
    intro n
    have hm : ⌊x * 2 ^ n⌋₊ + 1 ≤ ⌊y * 2 ^ n⌋₊ + 1 :=
      Nat.add_le_add_right (Nat.floor_mono (mul_le_mul_of_nonneg_right hxy (by positivity))) 1
    have h := dyadic_incr ρ hρ hq hlc n _ _ (⌊h * 2 ^ n⌋₊ + 1) hm
    unfold ap
    push_cast at h ⊢
    rw [← add_mul, ← add_mul]
    exact h
  have hs : ∀ r, 0 ≤ r → Antitone fun n => ap n r + ap n h :=
    fun r hr a b hab => add_le_add (ap_anti hr hab) (ap_anti hh hab)
  have hgt : ∀ r, 0 ≤ r → ∀ n, r + h < ap n r + ap n h :=
    fun r hr n => add_lt_add (ap_gt n hr) (ap_gt n hh)
  have hlim : ∀ r, 0 ≤ r → Tendsto (fun n => ap n r + ap n h) atTop (𝓝 (r + h)) :=
    fun r hr => (ap_tendsto hr).add (ap_tendsto hh)
  have t1 := V_to_W ρ hρ _ _ (hs y hy) (hgt y hy) (hlim y hy)
  have t2 := V_to_W ρ hρ _ _ (ap_anti hy) (fun n => ap_gt n hy) (ap_tendsto hy)
  have t3 := V_to_W ρ hρ _ _ (hs x hx) (hgt x hx) (hlim x hx)
  have t4 := V_to_W ρ hρ _ _ (ap_anti hx) (fun n => ap_gt n hx) (ap_tendsto hx)
  exact le_of_tendsto_of_tendsto' (t1.sub t2) (t3.sub t4) key

/-! ### Part G: nonincreasing increments and monotonicity give concavity -/

lemma avg_antitone (d : ℕ → ℝ) (hd : Antitone d) (k N : ℕ) (hkN : k ≤ N) :
    (k : ℝ) * ∑ i ∈ range N, d i ≤ N * ∑ i ∈ range k, d i := by
  have hsplit : ∑ i ∈ range N, d i = ∑ i ∈ range k, d i + ∑ i ∈ Ico k N, d i :=
    (Finset.sum_range_add_sum_Ico _ hkN).symm
  have h1 : ∑ i ∈ Ico k N, d i ≤ (N - k : ℝ) * d k := by
    have := Finset.sum_le_sum fun i (hi : i ∈ Ico k N) => hd (Finset.mem_Ico.1 hi).1
    simpa [Nat.cast_sub hkN] using this
  have h2 : (k : ℝ) * d k ≤ ∑ i ∈ range k, d i := by
    have := Finset.sum_le_sum fun i (hi : i ∈ range k) => hd (le_of_lt (Finset.mem_range.1 hi))
    simpa using this
  have hNk : (0 : ℝ) ≤ N - k := by have : (k : ℝ) ≤ N := by exact_mod_cast hkN
                                   linarith
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
    mul_le_mul_of_nonneg_left h2 hNk]

lemma incr_concave (f : ℝ → ℝ) (hmono : MonotoneOn f (Set.Ici 0))
    (hinc : ∀ x y h, 0 ≤ x → x ≤ y → 0 ≤ h → f (y + h) - f y ≤ f (x + h) - f x) :
    ConcaveOn ℝ (Set.Ici 0) f := by
  -- the key one-sided inequality
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f a + t * (f b - f a) ≤ f (a + t * (b - a)) := by
    intro a b ha hab t ht0 ht1
    have hfab : f a ≤ f b := hmono (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hab)) hab
    -- lattice version
    have hlat : ∀ N : ℕ, 0 < N → ∀ k : ℕ, k ≤ N →
        (k / N : ℝ) * (f b - f a) ≤ f (a + (k / N : ℝ) * (b - a)) - f a := by
      intro N hN k hk
      set ε := (b - a) / N with hε
      have hε0 : 0 ≤ ε := div_nonneg (by linarith) (Nat.cast_nonneg N)
      set d : ℕ → ℝ := fun i => f (a + (i + 1) * ε) - f (a + i * ε) with hd
      have hdanti : Antitone d := by
        refine antitone_nat_of_succ_le fun i => ?_
        have := hinc (a + i * ε) (a + (i + 1) * ε) ε (by positivity) (by nlinarith) hε0
        simp only [hd]
        push_cast
        have e1 : a + ((i : ℝ) + 1) * ε + ε = a + ((i : ℝ) + 1 + 1) * ε := by ring
        have e2 : a + (i : ℝ) * ε + ε = a + ((i : ℝ) + 1) * ε := by ring
        rw [e1, e2] at this
        exact this
      have htel : ∀ j : ℕ, ∑ i ∈ range j, d i = f (a + j * ε) - f a := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [hd]
          push_cast
          ring
      have hNε : a + (N : ℝ) * ε = b := by
        rw [hε, mul_div_cancel₀ _ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0)]; ring
      have havg := avg_antitone d hdanti k N hk
      rw [htel, htel, hNε] at havg
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have e3 : (k / N : ℝ) * (b - a) = k * ε := by rw [hε]; field_simp
      rw [e3, div_mul_eq_mul_div, div_le_iff₀ hNpos]
      linarith
    -- real version by approximation from below
    have hbound : ∀ N : ℕ, 0 < N →
        f a + t * (f b - f a) - (f b - f a) / N ≤ f (a + t * (b - a)) := by
      intro N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      set k := ⌊t * N⌋₊ with hk
      have hkN : k ≤ N := by
        rw [hk]
        refine Nat.floor_le_of_le ?_
        nlinarith
      have hkle : (k : ℝ) ≤ t * N := Nat.floor_le (by positivity)
      have hkge : t * N - 1 < (k : ℝ) := by
        have := Nat.lt_floor_add_one (t * N); linarith
      have hl := hlat N hN k hkN
      have hkN' : (k / N : ℝ) ≤ t := by rw [div_le_iff₀ hNpos]; linarith
      have hmon : f (a + (k / N : ℝ) * (b - a)) ≤ f (a + t * (b - a)) := by
        refine hmono (Set.mem_Ici.2 ?_) (Set.mem_Ici.2 ?_) ?_
        · have : 0 ≤ (k / N : ℝ) * (b - a) := mul_nonneg (by positivity) (by linarith)
          linarith
        · have : 0 ≤ t * (b - a) := mul_nonneg ht0 (by linarith)
          linarith
        · nlinarith
      have hfrac : t - 1 / N ≤ (k / N : ℝ) := by
        have h1 : t ≤ ((k : ℝ) + 1) / N := by rw [le_div_iff₀ hNpos]; linarith
        have e : ((k : ℝ) + 1) / N = k / N + 1 / N := by ring
        linarith
      have hfba : 0 ≤ f b - f a := by linarith
      have : (t - 1 / N) * (f b - f a) ≤ (k / N : ℝ) * (f b - f a) :=
        mul_le_mul_of_nonneg_right hfrac hfba
      have e4 : (t - 1 / N) * (f b - f a) = t * (f b - f a) - (f b - f a) / N := by ring
      linarith
    by_contra hcon
    push_neg at hcon
    set g := f a + t * (f b - f a) - f (a + t * (b - a)) with hg
    have hgpos : 0 < g := by linarith
    have hfba : 0 ≤ f b - f a := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((f b - f a) / g)
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hfba hgpos.le) hN
    have hN' : 0 < N := by exact_mod_cast hNpos
    have := hbound N hN'
    have h2 : (f b - f a) / N < g := by
      rw [div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ hgpos] at hN
      linarith
    linarith
  refine ⟨convex_Ici 0, ?_⟩
  intro a ha b hb α β hα hβ hαβ
  simp only [smul_eq_mul]
  rcases le_total a b with hab | hba
  · have h := key a b ha hab β hβ (by linarith)
    have e1 : α * a + β * b = a + β * (b - a) := by linear_combination a * hαβ
    have e2 : α * f a + β * f b = f a + β * (f b - f a) := by linear_combination f a * hαβ
    rw [e1, e2]; exact h
  · have h := key b a hb hba α hα (by linarith)
    have e1 : α * a + β * b = b + α * (a - b) := by linear_combination b * hαβ
    have e2 : α * f a + β * f b = f b + α * (f a - f b) := by linear_combination f b * hαβ
    rw [e1, e2]; exact h

end BrownB

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (hlc : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      (ρ {z : ℝ≥0 | η * x + (1 - η) * y < (z : ℝ)}).toReal
        ≤ (ρ {z : ℝ≥0 | x < (z : ℝ)}).toReal ^ η * (ρ {z : ℝ≥0 | y < (z : ℝ)}).toReal ^ (1 - η)) :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => (OWMR.renewalMeasure ρ (Set.Icc 0 x)).toReal) := by
  have hlc' : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      BrownB.sv ρ (η * x + (1 - η) * y) ≤ BrownB.sv ρ x ^ η * BrownB.sv ρ y ^ (1 - η) := hlc
  have hq : 0 < BrownB.sv ρ 0 := by
    by_contra h
    have h0 : BrownB.sv ρ 0 = 0 := le_antisymm (not_lt.1 h) (BrownB.sv_nonneg ρ 0)
    have hm : ρ {z : ℝ≥0 | (0 : ℝ) < (z : ℝ)} = 0 := by
      unfold BrownB.sv at h0
      rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
      · exact h
      · exact absurd h (measure_ne_top _ _)
    have hae : (fun x : ℝ≥0 => (x : ℝ≥0∞)) =ᵐ[ρ] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun x hx => ?_) hm
      simp only [Set.mem_setOf_eq, Pi.zero_apply, ENNReal.coe_eq_zero] at hx ⊢
      exact lt_of_le_of_ne x.2 (Ne.symm (by exact_mod_cast hx))
    have : ∫⁻ x, (x : ℝ≥0∞) ∂ρ = 0 := by rw [lintegral_congr_ae hae]; simp
    rw [this] at hρ
    exact lt_irrefl _ hρ
  refine BrownB.incr_concave _ ?_ ?_
  · intro x hx y hy hxy
    have hfin : OWMR.renewalMeasure ρ (Set.Icc 0 y) ≠ ∞ :=
      ne_top_of_le_ne_top (OWMR.renewalMeasure_Ico_lt_top ρ hρ (y + 1)).ne
        (measure_mono (Set.Icc_subset_Ico_right (by linarith)))
    exact ENNReal.toReal_mono hfin (measure_mono (Set.Icc_subset_Icc_right hxy))
  · intro x y h hx hxy hh
    exact BrownB.W_incr ρ hρ hq hlc' x y h hx hxy hh

end

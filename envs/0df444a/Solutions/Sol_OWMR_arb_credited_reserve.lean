-- Prove2me | solution 1 for OWMR.arb_credited_reserve
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:27.87455+00:00
-- url     : https://prove2.me/submissions/a44cfaa1-62eb-4f12-a2de-c6843a8b8dd7

import Definitions.Def_owmr_consolidation_policy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory
open scoped ENNReal
open OWMR

section sp

variable (Q : ℝ) (A : ℕ → ℝ)

private lemma sp_zero (θ : ℝ) :
    shippedPath Q θ A 0 = if crossesThreshold Q θ 0 (A 0) then A 0 else 0 := rfl

private lemma sp_succ (θ : ℝ) (k : ℕ) :
    shippedPath Q θ A (k + 1)
      = if crossesThreshold Q θ (A k) (A (k + 1)) then A (k + 1) else shippedPath Q θ A k := rfl

private lemma sp_bounds (hA0 : 0 ≤ A 0) (hA : Monotone A) (θ : ℝ) :
    ∀ k, 0 ≤ shippedPath Q θ A k ∧ shippedPath Q θ A k ≤ A k := by
  intro k
  induction k with
  | zero =>
    rw [sp_zero]
    split_ifs
    · exact ⟨hA0, le_rfl⟩
    · exact ⟨le_rfl, hA0⟩
  | succ k ih =>
    rw [sp_succ]
    split_ifs
    · exact ⟨hA0.trans (hA (Nat.zero_le _)), le_rfl⟩
    · exact ⟨ih.1, ih.2.trans (hA (Nat.le_succ k))⟩

private lemma sp_full (hQ : 0 < Q) (hA : Monotone A) (hAQ : ∀ k, A k ≤ Q) (θ : ℝ) :
    ∀ k, A k = Q → shippedPath Q θ A k = Q := by
  intro k
  induction k with
  | zero =>
    intro h
    rw [sp_zero, if_pos (Or.inr (Or.inr ⟨hQ, h⟩)), h]
  | succ k ih =>
    intro h
    rw [sp_succ]
    by_cases hk : A k = Q
    · split_ifs
      · exact h
      · exact ih hk
    · have : A k < Q := lt_of_le_of_ne (hAQ k) hk
      rw [if_pos (Or.inr (Or.inr ⟨this, h⟩)), h]

/-- Thresholds already reached are remembered by the shipped quantity. -/
private lemma sp_memory (hA : Monotone A) (θ : ℝ) (hθ : 0 < θ) (hQ : 0 < Q) :
    ∀ k, (3 * Q / 4 * θ ≤ A k → 3 * Q / 4 * θ ≤ shippedPath Q θ A k) ∧
      (θ < 1 / 3 → 3 * Q / 4 * (1 + θ) ≤ A k → 3 * Q / 4 * (1 + θ) ≤ shippedPath Q θ A k) := by
  have hc1 : 0 < 3 * Q / 4 * θ := by positivity
  have hc2 : 0 < 3 * Q / 4 * (1 + θ) := by positivity
  intro k
  induction k with
  | zero =>
    refine ⟨fun h => ?_, fun h3 h => ?_⟩
    · rw [sp_zero, if_pos (Or.inl ⟨hc1, h⟩)]; exact h
    · rw [sp_zero, if_pos (Or.inr (Or.inl ⟨h3, hc2, h⟩))]; exact h
  | succ k ih =>
    refine ⟨fun h => ?_, fun h3 h => ?_⟩
    · rw [sp_succ]
      split_ifs with hc
      · exact h
      · have : 3 * Q / 4 * θ ≤ A k := by
          by_contra hlt
          exact hc (Or.inl ⟨lt_of_not_ge hlt, h⟩)
        exact ih.1 this
    · rw [sp_succ]
      split_ifs with hc
      · exact h
      · have : 3 * Q / 4 * (1 + θ) ≤ A k := by
          by_contra hlt
          exact hc (Or.inr (Or.inl ⟨h3, lt_of_not_ge hlt, h⟩))
        exact ih.2 h3 this

/-- A level is crossed in at most one period. -/
private lemma cross_once (hA : Monotone A) (c : ℝ) (hc : 0 < c) (T : ℕ) :
    ∑ k ∈ Finset.range T, (if (if k = 0 then 0 else A (k - 1)) < c ∧ c ≤ A k then (1 : ℝ) else 0)
      ≤ 1 := by
  rw [Finset.sum_boole]
  have : ((Finset.range T).filter
      (fun k => (if k = 0 then 0 else A (k - 1)) < c ∧ c ≤ A k)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hab
    rcases lt_or_gt_of_ne hab with h | h
    · -- `a < b`: then the level was already reached before `b`
      have hb0 : b ≠ 0 := by omega
      have h1 : A a ≤ A (b - 1) := hA (by omega)
      rw [if_neg hb0] at hb
      linarith [ha.2.2, hb.2.1]
    · have ha0 : a ≠ 0 := by omega
      have h1 : A b ≤ A (a - 1) := hA (by omega)
      rw [if_neg ha0] at ha
      linarith [hb.2.2, ha.2.1]
  exact_mod_cast this

private lemma cross_count (hA : Monotone A) (hAQ : ∀ k, A k ≤ Q) (hQ : 0 < Q) (θ : ℝ) (hθ : 0 < θ)
    (T : ℕ) :
    ∑ k ∈ Finset.range T,
        (if crossesThreshold Q θ (if k = 0 then 0 else A (k - 1)) (A k) then (1 : ℝ) else 0)
      ≤ 1 + if θ < 1 / 3 then 2 else 1 := by
  set pv : ℕ → ℝ := fun k => if k = 0 then 0 else A (k - 1) with hpv
  have h1 := cross_once A hA (3 * Q / 4 * θ) (by positivity) T
  have h2 := cross_once A hA (3 * Q / 4 * (1 + θ)) (by positivity) T
  have h3 := cross_once A hA Q hQ T
  have hpt : ∀ k, (if crossesThreshold Q θ (pv k) (A k) then (1 : ℝ) else 0)
      ≤ (if pv k < 3 * Q / 4 * θ ∧ 3 * Q / 4 * θ ≤ A k then 1 else 0)
        + (if θ < 1 / 3 then (if pv k < 3 * Q / 4 * (1 + θ) ∧ 3 * Q / 4 * (1 + θ) ≤ A k
            then 1 else 0) else 0)
        + (if pv k < Q ∧ Q ≤ A k then 1 else 0) := by
    intro k
    by_cases hc : crossesThreshold Q θ (pv k) (A k)
    · rw [if_pos hc]
      rcases hc with h | ⟨h3', h⟩ | ⟨h, h'⟩
      · rw [if_pos h]
        have : (0 : ℝ) ≤ (if θ < 1 / 3 then (if pv k < 3 * Q / 4 * (1 + θ) ∧
            3 * Q / 4 * (1 + θ) ≤ A k then 1 else 0) else 0) := by split_ifs <;> norm_num
        have : (0 : ℝ) ≤ (if pv k < Q ∧ Q ≤ A k then 1 else 0) := by split_ifs <;> norm_num
        linarith
      · rw [if_pos h3', if_pos h]
        have : (0 : ℝ) ≤ (if pv k < 3 * Q / 4 * θ ∧ 3 * Q / 4 * θ ≤ A k then 1 else 0) := by
          split_ifs <;> norm_num
        have : (0 : ℝ) ≤ (if pv k < Q ∧ Q ≤ A k then 1 else 0) := by split_ifs <;> norm_num
        linarith
      · rw [if_pos (show pv k < Q ∧ Q ≤ A k from ⟨h, h'.ge⟩)]
        have : (0 : ℝ) ≤ (if pv k < 3 * Q / 4 * θ ∧ 3 * Q / 4 * θ ≤ A k then 1 else 0) := by
          split_ifs <;> norm_num
        have : (0 : ℝ) ≤ (if θ < 1 / 3 then (if pv k < 3 * Q / 4 * (1 + θ) ∧
            3 * Q / 4 * (1 + θ) ≤ A k then 1 else 0) else 0) := by split_ifs <;> norm_num
        linarith
    · rw [if_neg hc]
      have h1 : (0 : ℝ) ≤ (if pv k < 3 * Q / 4 * θ ∧ 3 * Q / 4 * θ ≤ A k then 1 else 0) := by
        split_ifs <;> norm_num
      have h2 : (0 : ℝ) ≤ (if θ < 1 / 3 then (if pv k < 3 * Q / 4 * (1 + θ) ∧
          3 * Q / 4 * (1 + θ) ≤ A k then 1 else 0) else 0) := by split_ifs <;> norm_num
      have h3 : (0 : ℝ) ≤ (if pv k < Q ∧ Q ≤ A k then 1 else 0) := by split_ifs <;> norm_num
      linarith
  calc ∑ k ∈ Finset.range T, (if crossesThreshold Q θ (pv k) (A k) then (1 : ℝ) else 0)
      ≤ ∑ k ∈ Finset.range T, ((if pv k < 3 * Q / 4 * θ ∧ 3 * Q / 4 * θ ≤ A k then 1 else 0)
        + (if θ < 1 / 3 then (if pv k < 3 * Q / 4 * (1 + θ) ∧ 3 * Q / 4 * (1 + θ) ≤ A k
            then 1 else 0) else 0)
        + (if pv k < Q ∧ Q ≤ A k then 1 else 0)) := Finset.sum_le_sum fun k _ => hpt k
    _ ≤ 1 + (if θ < 1 / 3 then 1 else 0) + 1 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      refine add_le_add (add_le_add h1 ?_) h3
      split_ifs
      · exact h2
      · simp
    _ = 1 + if θ < 1 / 3 then 2 else 1 := by split_ifs <;> norm_num

end sp

section integ

/-- `∫_0^b (s - z)⁺ ds = ((b - z)⁺)² / 2`. -/
private lemma integral_pos_part (b z : ℝ) (hb : 0 ≤ b) (hz : 0 ≤ z) :
    ∫ s in (0 : ℝ)..b, max (s - z) 0 = max (b - z) 0 ^ 2 / 2 := by
  rcases le_or_gt b z with hbz | hzb
  · rw [max_eq_right (by linarith : b - z ≤ 0)]
    have : ∀ s ∈ Set.uIcc (0 : ℝ) b, max (s - z) 0 = (0 : ℝ) := fun s hs => by
      rw [Set.uIcc_of_le hb] at hs
      exact max_eq_right (by linarith [hs.2])
    rw [intervalIntegral.integral_congr this]
    simp
  · rw [max_eq_left (by linarith : 0 ≤ b - z)]
    have hc : Continuous fun s : ℝ => max (s - z) 0 := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := z)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have h1 : ∀ s ∈ Set.uIcc (0 : ℝ) z, max (s - z) 0 = (0 : ℝ) := fun s hs => by
      rw [Set.uIcc_of_le hz] at hs
      exact max_eq_right (by linarith [hs.2])
    have h2 : ∀ s ∈ Set.uIcc z b, max (s - z) 0 = s - z := fun s hs => by
      rw [Set.uIcc_of_le hzb.le] at hs
      exact max_eq_left (by linarith [hs.1])
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_congr h2,
      intervalIntegral.integral_comp_sub_right (fun s => s), integral_id]
    simp

/-- Lebesgue integral over `(α, β]` of a continuous nonnegative function as an interval integral. -/
private lemma lint_Ioc (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (α β : ℝ)
    (hαβ : α ≤ β) :
    ∫⁻ θ in Set.Ioc α β, ENNReal.ofReal (f θ) = ENNReal.ofReal (∫ θ in α..β, f θ) := by
  rw [intervalIntegral.integral_of_le hαβ, ofReal_integral_eq_lintegral_ofReal]
  · exact (hf.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · exact Filter.Eventually.of_forall hf0

/-- The averaged credited reserve of the sawtooth `θ ↦ (x - bθ) mod b`. -/
private lemma sawtooth (b x' z : ℝ) (hb : 0 < b) (hx0 : 0 ≤ x') (hxb : x' < b) (hz : 0 ≤ z) :
    ∫⁻ θ in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((if b * θ ≤ x' then x' - b * θ else x' + b - b * θ) - z)
      ≤ ENNReal.ofReal (max (b - z) 0 ^ 2 / (2 * b)) := by
  set c := x' / b with hc
  have hc0 : 0 ≤ c := div_nonneg hx0 hb.le
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hb]; exact hxb.le
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc 0 c ∪ Set.Ioc c 1 := fun θ hθ => by
    rcases le_or_gt θ c with h | h
    · exact Or.inl ⟨hθ.1, h⟩
    · exact Or.inr ⟨h, hθ.2.le⟩
  have hp1 : ∫⁻ θ in Set.Ioc 0 c,
        ENNReal.ofReal ((if b * θ ≤ x' then x' - b * θ else x' + b - b * θ) - z)
      = ∫⁻ θ in Set.Ioc 0 c, ENNReal.ofReal (max (x' - b * θ - z) 0) := by
    refine setLIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    have : b * θ ≤ x' := by
      have := mul_le_mul_of_nonneg_left hθ.2 hb.le
      rwa [hc, mul_div_cancel₀ _ hb.ne'] at this
    rw [if_pos this, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (by positivity)]
  have hp2 : ∫⁻ θ in Set.Ioc c 1,
        ENNReal.ofReal ((if b * θ ≤ x' then x' - b * θ else x' + b - b * θ) - z)
      = ∫⁻ θ in Set.Ioc c 1, ENNReal.ofReal (max (x' + b - b * θ - z) 0) := by
    refine setLIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    have : ¬ b * θ ≤ x' := by
      have := mul_lt_mul_of_pos_left hθ.1 hb
      rw [hc, mul_div_cancel₀ _ hb.ne'] at this
      linarith
    rw [if_neg this, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (by positivity)]
  have hg : Continuous fun s : ℝ => max (s - z) 0 := by fun_prop
  have hI1 : ∫ θ in (0 : ℝ)..c, max (x' - b * θ - z) 0 = b⁻¹ * ∫ s in (0 : ℝ)..x', max (s - z) 0 := by
    have := intervalIntegral.integral_comp_sub_mul (fun s => max (s - z) 0) (a := 0) (b := c)
      hb.ne' x'
    rw [this, hc, mul_div_cancel₀ _ hb.ne', sub_self, mul_zero, sub_zero, smul_eq_mul]
  have hI2 : ∫ θ in c..1, max (x' + b - b * θ - z) 0 = b⁻¹ * ∫ s in x'..b, max (s - z) 0 := by
    have := intervalIntegral.integral_comp_sub_mul (fun s => max (s - z) 0) (a := c) (b := 1)
      hb.ne' (x' + b)
    rw [this, hc, mul_div_cancel₀ _ hb.ne', mul_one, smul_eq_mul]
    congr 2 <;> ring
  calc ∫⁻ θ in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((if b * θ ≤ x' then x' - b * θ else x' + b - b * θ) - z)
      ≤ ∫⁻ θ in Set.Ioc 0 c ∪ Set.Ioc c 1,
          ENNReal.ofReal ((if b * θ ≤ x' then x' - b * θ else x' + b - b * θ) - z) :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ θ in Set.Ioc 0 c,
          ENNReal.ofReal ((if b * θ ≤ x' then x' - b * θ else x' + b - b * θ) - z))
        + ∫⁻ θ in Set.Ioc c 1,
          ENNReal.ofReal ((if b * θ ≤ x' then x' - b * θ else x' + b - b * θ) - z) :=
        lintegral_union_le _ _ _
    _ = ENNReal.ofReal (∫ θ in (0 : ℝ)..c, max (x' - b * θ - z) 0)
        + ENNReal.ofReal (∫ θ in c..1, max (x' + b - b * θ - z) 0) := by
        rw [hp1, hp2, lint_Ioc _ (by fun_prop) (fun _ => le_max_right _ _) _ _ hc0,
          lint_Ioc _ (by fun_prop) (fun _ => le_max_right _ _) _ _ hc1]
    _ = ENNReal.ofReal (b⁻¹ * ∫ s in (0 : ℝ)..b, max (s - z) 0) := by
        rw [hI1, hI2, ← ENNReal.ofReal_add, ← mul_add,
          intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
            (hg.intervalIntegrable _ _)]
        · exact mul_nonneg (inv_nonneg.2 hb.le)
            (intervalIntegral.integral_nonneg hx0 fun s _ => le_max_right _ _)
        · exact mul_nonneg (inv_nonneg.2 hb.le)
            (intervalIntegral.integral_nonneg hxb.le fun s _ => le_max_right _ _)
    _ = ENNReal.ofReal (max (b - z) 0 ^ 2 / (2 * b)) := by
        rw [integral_pos_part b z hb.le hz]
        congr 1
        field_simp

end integ

private lemma seven_thirds :
    ∫⁻ θ in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 + if θ < 1 / 3 then 2 else 1)
      = ENNReal.ofReal (7 / 3) := by
  have hU : Set.Ioo (0 : ℝ) 1 = Set.Ioo 0 (1 / 3) ∪ Set.Ico (1 / 3) 1 := by
    ext θ
    simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Ico]
    constructor
    · rintro ⟨h0, h1⟩
      rcases lt_or_ge θ (1 / 3) with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · exact ⟨h0, by linarith⟩
      · exact ⟨by linarith, h1⟩
  have hD : Disjoint (Set.Ioo (0 : ℝ) (1 / 3)) (Set.Ico (1 / 3) 1) := by
    rw [Set.disjoint_left]
    intro θ h1 h2
    linarith [h1.2, h2.1]
  rw [hU, lintegral_union measurableSet_Ico hD]
  have e1 : ∫⁻ θ in Set.Ioo (0 : ℝ) (1 / 3), ENNReal.ofReal (1 + if θ < 1 / 3 then 2 else 1)
      = ∫⁻ _θ in Set.Ioo (0 : ℝ) (1 / 3), ENNReal.ofReal 3 := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    rw [if_pos hθ.2]; norm_num
  have e2 : ∫⁻ θ in Set.Ico (1 / 3 : ℝ) 1, ENNReal.ofReal (1 + if θ < 1 / 3 then 2 else 1)
      = ∫⁻ _θ in Set.Ico (1 / 3 : ℝ) 1, ENNReal.ofReal 2 := by
    refine setLIntegral_congr_fun measurableSet_Ico fun θ hθ => ?_
    rw [if_neg (not_lt.2 hθ.1)]; norm_num
  rw [e1, e2, setLIntegral_const, setLIntegral_const, Real.volume_Ioo, Real.volume_Ico,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem solution (Q : ℝ) (A : ℕ → ℝ) (hQ : 0 < Q) (hA0 : 0 ≤ A 0) (hA : Monotone A)
    (hAQ : ∀ k, A k ≤ Q) :
    (∀ θ k, 0 ≤ shippedPath Q θ A k ∧ shippedPath Q θ A k ≤ A k) ∧
    (∀ θ k, A k = Q → shippedPath Q θ A k = Q) ∧
    (∀ θ T, 0 < θ →
      ∑ k ∈ Finset.range T,
          (if crossesThreshold Q θ (if k = 0 then 0 else A (k - 1)) (A k) then (1 : ℝ) else 0)
        ≤ 1 + if θ < 1 / 3 then 2 else 1) ∧
    (∀ k z, 0 ≤ z → A k < Q →
      ∫⁻ θ in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (A k - shippedPath Q θ A k - z)
        ≤ ENNReal.ofReal (max (3 * Q / 4 - z) 0 ^ 2 / (3 * Q / 2))) ∧
    ∫⁻ θ in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 + if θ < 1 / 3 then 2 else 1)
      = ENNReal.ofReal (7 / 3) := by
  refine ⟨fun θ k => sp_bounds Q A hA0 hA θ k, fun θ k h => sp_full Q A hQ hA hAQ θ k h,
    fun θ T hθ => cross_count Q A hA hAQ hQ θ hθ T, fun k z hz hk => ?_, seven_thirds⟩
  set b : ℝ := 3 * Q / 4 with hb
  have hb0 : 0 < b := by positivity
  set x := A k with hx
  have hx0 : 0 ≤ x := hA0.trans (hA (Nat.zero_le k))
  set x' : ℝ := if x < b then x else x - b with hx'
  have hx'0 : 0 ≤ x' := by rw [hx']; split_ifs with h <;> linarith
  have hx'b : x' < b := by rw [hx']; split_ifs with h <;> linarith
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (x - shippedPath Q θ A k - z)
      ≤ ENNReal.ofReal ((if b * θ ≤ x' then x' - b * θ else x' + b - b * θ) - z) := by
    intro θ hθ
    apply ENNReal.ofReal_le_ofReal
    have hm := sp_memory Q A hA θ hθ.1 hQ k
    have hsb := sp_bounds Q A hA0 hA θ k
    rw [← hx] at hm hsb
    have hbθ : b * θ = 3 * Q / 4 * θ := rfl
    have hbθ' : b * θ + b = 3 * Q / 4 * (1 + θ) := by rw [hb]; ring
    rw [hx']
    by_cases hxb : x < b
    · rw [if_pos hxb]
      split_ifs with h
      · linarith [hm.1 (by linarith)]
      · nlinarith [hθ.2]
    · rw [if_neg hxb]
      split_ifs with h
      · -- the second threshold has been reached
        have h3 : θ < 1 / 3 := by nlinarith
        linarith [hm.2 h3 (by linarith)]
      · have : b * θ < b := by nlinarith [hθ.2]
        linarith [hm.1 (by linarith)]
  calc ∫⁻ θ in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (x - shippedPath Q θ A k - z)
      ≤ ∫⁻ θ in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((if b * θ ≤ x' then x' - b * θ else x' + b - b * θ) - z) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ENNReal.ofReal (max (b - z) 0 ^ 2 / (2 * b)) := sawtooth b x' z hb0 hx'0 hx'b hz
    _ = ENNReal.ofReal (max (3 * Q / 4 - z) 0 ^ 2 / (3 * Q / 2)) := by
        rw [hb]; congr 2; ring

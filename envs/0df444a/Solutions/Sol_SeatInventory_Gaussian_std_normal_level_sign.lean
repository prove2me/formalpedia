-- Prove2me | solution 1 for SeatInventory.Gaussian.std_normal_level_sign
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:00:41.739985+00:00
-- url     : https://prove2.me/submissions/f6287aeb-da58-4bff-92d1-99cca1f7d0f9

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory in
theorem a9ec_tail_strictAnti (m : ℝ) (v : NNReal) (hv : v ≠ 0) {a b : ℝ} (hab : a < b) :
    ((gaussianReal m v) (Set.Ici b)).toReal < ((gaussianReal m v) (Set.Ici a)).toReal := by
  set μ := gaussianReal m v
  have hsplit : μ (Set.Ici a) = μ (Set.Ico a b) + μ (Set.Ici b) := by
    rw [← Set.Ico_union_Ici_eq_Ici hab.le]
    exact measure_union (Set.disjoint_left.2 fun x hx hx' => (not_le.2 hx.2) hx') measurableSet_Ici
  have hpos : μ (Set.Ico a b) ≠ 0 := by
    intro h
    have h2 := gaussianReal_absolutelyContinuous' m hv h
    rw [Real.volume_Ico] at h2
    simp at h2
    linarith
  rw [ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _), hsplit]
  rw [add_comm]
  exact ENNReal.lt_add_right (measure_ne_top _ _) hpos

open MeasureTheory ProbabilityTheory in
theorem a9ec_tail_mean (m : ℝ) (v : NNReal) (hv : v ≠ 0) :
    ((gaussianReal m v) (Set.Ici m)).toReal = 1 / 2 := by
  set μ := gaussianReal m v
  have hsym : μ (Set.Ici m) = μ (Set.Iic m) := by
    have hmap : μ.map (fun x => (2 * m) - x) = μ := by
      show (gaussianReal m v).map (fun x => (2 * m) - x) = gaussianReal m v
      rw [gaussianReal_map_const_sub]
      congr 1; ring
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply (by fun_prop) measurableSet_Ici]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  have hsing : μ {m} = 0 := gaussianReal_absolutelyContinuous m hv (Real.volume_singleton)
  have hui := measure_union_add_inter (μ := μ) (Set.Iic m) (measurableSet_Ici (a := m))
  rw [Set.Iic_union_Ici, Set.Iic_inter_Ici, Set.Icc_self, hsing, measure_univ, add_zero,
    ← hsym] at hui
  have h1 : (μ (Set.Ici m)).toReal + (μ (Set.Ici m)).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← hui]; simp
  linarith

open SeatInventory.Gaussian in
theorem a9ec_std_tail_lt {a b : ℝ} (hab : a < b) : tailProb stdNormal b < tailProb stdNormal a :=
  a9ec_tail_strictAnti 0 1 one_ne_zero hab

open SeatInventory.Gaussian in
theorem a9ec_std_tail_zero : tailProb stdNormal 0 = 1 / 2 :=
  a9ec_tail_mean 0 1 one_ne_zero

open SeatInventory.Gaussian in
theorem solution (f₁ f₂ Z : ℝ) (hf₂ : 0 < f₂) (hf : f₂ < f₁)
    (hZ : IsStdNormalLevel f₁ f₂ Z) :
    (1 / 2 < f₂ / f₁ → Z < 0) ∧ (f₂ / f₁ < 1 / 2 → 0 < Z) ∧ (f₂ / f₁ = 1 / 2 → Z = 0) ∧
      (f₂ / f₁ = 1 / 2 → ∀ rbar σ S : ℝ, 0 < σ → IsProtectionLevel rbar σ f₁ f₂ S → S = rbar) := by
  unfold IsStdNormalLevel at hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    by_contra hc
    replace hc := not_lt.mp hc
    rcases hc.lt_or_eq with hc | hc
    · have := a9ec_std_tail_lt hc; rw [a9ec_std_tail_zero] at this; linarith
    · subst hc; rw [a9ec_std_tail_zero] at hZ; linarith
  · intro h
    by_contra hc
    replace hc := not_lt.mp hc
    rcases hc.lt_or_eq with hc | hc
    · have := a9ec_std_tail_lt hc; rw [a9ec_std_tail_zero] at this; linarith
    · rw [hc, a9ec_std_tail_zero] at hZ; linarith
  · intro h
    rcases lt_trichotomy Z 0 with hc | hc | hc
    · have := a9ec_std_tail_lt hc; rw [a9ec_std_tail_zero] at this; linarith
    · exact hc
    · have := a9ec_std_tail_lt hc; rw [a9ec_std_tail_zero] at this; linarith
  · intro h rbar σ S hσ hS
    unfold IsProtectionLevel tailProb gaussianLaw at hS
    have hv : (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal) ≠ 0 := by
      intro h0
      have := congrArg Subtype.val h0
      simp at this
      linarith
    have hm := a9ec_tail_mean rbar _ hv
    rcases lt_trichotomy S rbar with hc | hc | hc
    · have := a9ec_tail_strictAnti rbar _ hv hc; linarith
    · exact hc
    · have := a9ec_tail_strictAnti rbar _ hv hc; linarith

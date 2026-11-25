-- Prove2me | solution 1 for PI.SSU.main_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:35.678482+00:00
-- url     : https://prove2.me/submissions/d9676a0a-e663-4d7c-a9a9-49f9544298be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_Complete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_ZeroOfCoef
import Theorems.Thm_PI_SSU_normF_diff
import Theorems.Thm_PI_SSU_coef_lin
import Theorems.Thm_PI_SSU_zero_of_coef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SSU
open Complex
open Classical
namespace PI.SSU
theorem _root_.solution (hK : KeyP) (hA : AreaLat) : SigmaStarUniq := by
  intro a b hs G G' hG hG'
  have harea : area (lat2 a b) = |((starRingEnd ℂ) a * b).im| := (hA a b hs).1
  have ha0 : a ≠ 0 := by rintro rfl; simp at hs
  have hma : a ∈ lat2 a b := AddSubgroup.subset_closure (by simp)
  have hmb : b ∈ lat2 a b := AddSubgroup.subset_closure (by simp)
  have hp0 : (if a / 2 ∈ lat2 a b then (1:ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  have hq0 : (if b / 2 ∈ lat2 a b then (1:ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  have hz : a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b =
      -(2 * I * ((((starRingEnd ℂ) a * b).im : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp <;> ring
  obtain ⟨k, hk1, hk⟩ : ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      (Real.pi : ℂ) / ((area (lat2 a b) : ℝ) : ℂ) * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
        -(2 * (Real.pi : ℂ) * I * k) := by
    rw [harea, hz]
    have hs' : ((((starRingEnd ℂ) a * b).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [abs_of_neg hneg]; push_cast; field_simp
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [abs_of_pos hpos]; push_cast; field_simp
  have FE_of : ∀ F : ℂ → ℂ, (∀ ω ∈ lat2 a b, ∀ z, U1 (lat2 a b) ω F z =
      (if ω / 2 ∈ lat2 a b then 1 else -1) * F z) →
      FE ((area (lat2 a b) : ℝ) : ℂ) a (if a / 2 ∈ lat2 a b then 1 else -1) F ∧
      FE ((area (lat2 a b) : ℝ) : ℂ) b (if b / 2 ∈ lat2 a b then 1 else -1) F :=
    fun F h => ⟨fun z => h a hma z, fun z => h b hmb z⟩
  obtain ⟨hGa, hGb⟩ := FE_of G hG.2.2.2
  obtain ⟨hG'a, hG'b⟩ := FE_of G' hG'.2.2.2
  have Z := zero_of_coef hK a b _ _ _ k ha0 hp0 hq0 hk1 hk
  set c : (ℂ → ℂ) → ℂ := fun F => coef (normF a ((area (lat2 a b) : ℝ) : ℂ)
    (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) F) 0 with hc
  have hH := Z (fun z => c G * G' z - c G' * G z) (by have := hG.1; have := hG'.1; fun_prop)
    (fun z => by linear_combination c G * hG'a z - c G' * hGa z)
    (fun z => by linear_combination c G * hG'b z - c G' * hGb z)
    (by
      have e : normF a ((area (lat2 a b) : ℝ) : ℂ) (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1))
          (fun z => c G * G' z - c G' * G z) = fun u => c G * normF a ((area (lat2 a b) : ℝ) : ℂ)
            (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) G' u - c G' * normF a
            ((area (lat2 a b) : ℝ) : ℂ) (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) G u := by
        funext u; simp only [normF]; ring
      rw [e, coef_lin _ _ (normF_diff _ _ _ _ hG'.1).continuous (normF_diff _ _ _ _ hG.1).continuous]
      simp only [hc]; ring)
  have e : (fun z => c G * G' z) = (fun z => c G' * G z) :=
    funext fun z => sub_eq_zero.1 (congrFun hH z)
  have hd := congrArg (fun F => deriv F 0) e
  rw [deriv_const_mul _ (hG'.1 0), deriv_const_mul _ (hG.1 0), hG.2.1, hG'.2.1] at hd
  by_cases h0 : c G = 0
  · exfalso
    have hG0 := Z G hG.1 hGa hGb h0
    have := hG.2.1
    rw [hG0] at this
    simp at this
  · funext z
    have := congrFun e z
    simp only [mul_one] at hd
    rw [← hd] at this
    exact (mul_left_cancel₀ h0 this).symm
end PI.SSU

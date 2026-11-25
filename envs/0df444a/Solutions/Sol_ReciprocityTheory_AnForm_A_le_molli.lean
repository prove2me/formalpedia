-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.le_molli
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:18.511954+00:00
-- url     : https://prove2.me/submissions/0050841a-e25e-4531-899d-7c51264c475e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_smul_measurePreserving
import Theorems.Thm_ReciprocityTheory_AnForm_A_circle_fubini
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_circle_inv
import Theorems.Thm_ReciprocityTheory_AnForm_A_phiC
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_eq_C
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_scaled
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_scaled
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_lt_of_scaled_ne_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_hasCompactSupport
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink U ε) : φ z ≤ molli ρ ε φ z := by
  set C := closedBall z ε with hCdef
  obtain ⟨hm, hi⟩ := phiC hU hφ (isCompact_closedBall z ε) hz
  have hP : Continuous (Function.uncurry fun (ζ : ℂ) (y : Fin D → ℂ) => z - ζ • y) :=
    continuous_const.sub (continuous_fst.smul continuous_snd)
  have hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (fun y : Fin D → ℂ => z - ζ • y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => z - ζ • y) := by
    intro ζ hζ
    obtain ⟨h1, h2⟩ := smul_measurePreserving (D := D) hζ
    exact ⟨(Measure.measurePreserving_sub_left volume z).comp h1,
      (Homeomorph.subLeft z).measurableEmbedding.comp h2⟩
  obtain ⟨hFint, hF⟩ := circle_fubini hm hi (scaled_contDiff ρ ε).continuous
    (scaled_hasCompactSupport ρ hε) hP hPm
  have hrot : ∀ ζ ∈ sphere (0 : ℂ) |1|,
      (∫ y, ρ.scaled ε y * C.indicator φ (z - ζ • y)) = molli ρ ε φ z := by
    intro ζ hζ
    have hζ' : ‖ζ‖ = 1 := by simpa using hζ
    obtain ⟨h1, h2⟩ := smul_measurePreserving (D := D) hζ'
    have := h1.integral_comp h2 (fun u => ρ.scaled ε u * C.indicator φ (z - u))
    rw [molli_eq_C ρ hε (subset_refl _), ← this]
    congr 1
    funext y
    rw [scaled_circle_inv ρ hζ']
  rw [circleAverage_congr_sphere hrot, circleAverage_const] at hF
  rw [← hF]
  calc φ z = ∫ y, ρ.scaled ε y * φ z := by
        rw [integral_mul_const, integral_scaled ρ hε, one_mul]
    _ ≤ _ := by
      refine integral_mono ((integrable_scaled ρ hε).mul_const _) hFint fun y => ?_
      by_cases hy : ρ.scaled ε y = 0
      · simp [hy]
      refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε y)
      have hyε := (norm_lt_of_scaled_ne_zero ρ hε hy).le
      have hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • (-y) ∈ C := by
        intro ζ hζ
        rw [hCdef, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_neg]
        nlinarith [norm_nonneg ζ, norm_nonneg y]
      obtain ⟨-, hmean⟩ := hφ.2 z (-y) (fun ζ hζ => hz (hdisc ζ hζ))
      refine hmean.trans (le_of_eq (circleAverage_congr_sphere fun ζ hζ => ?_))
      have hζ' : ‖ζ‖ ≤ 1 := by simp at hζ; linarith
      have h := hdisc ζ hζ'
      rw [smul_neg, ← sub_eq_add_neg] at h ⊢
      rw [indicator_of_mem h]
end ReciprocityTheory.AnForm.A

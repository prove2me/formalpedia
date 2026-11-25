-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.molli_le_polyMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:22.029049+00:00
-- url     : https://prove2.me/submissions/44b1c705-ec01-4d81-9e06-bd8e080f27d0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_phiC
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_eq_C
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_kC
import Theorems.Thm_ReciprocityTheory_AnForm_A_mem_ball_sub
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_scaled
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_scaled
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
theorem _root_.solution (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) : molli ρ ε φ z ≤ polyMax φ z ε := by
  obtain ⟨-, hi⟩ := phiC hU hφ (isCompact_closedBall z ε) hz
  rw [molli_eq_C ρ hε (subset_refl _)]
  calc _ ≤ ∫ y, ρ.scaled ε y * polyMax φ z ε := by
        refine integral_mono (integrable_kC ρ hε hi z) ((integrable_scaled ρ hε).mul_const _)
          fun y => ?_
        by_cases hy : ρ.scaled ε y = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε y)
        have hmem := mem_ball_sub ρ hε hy z
        rw [indicator_of_mem hmem]
        exact (hφ.1.mono hz).bddAbove_of_isCompact (isCompact_closedBall z ε) |>.elim
          fun _ _ => le_csSup ((hφ.1.mono hz).bddAbove_of_isCompact (isCompact_closedBall z ε))
            (mem_image_of_mem φ hmem)
    _ = polyMax φ z ε := by rw [integral_mul_const, integral_scaled ρ hε, one_mul]
end ReciprocityTheory.AnForm.A

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_mem_torsion_of_b95fcaef923b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:15.054911+00:00
-- url     : https://prove2.me/submissions/6a79b075-762d-4508-915a-683332ba2e71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_place_apply_ef36c5cc456e
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_abs_norm_eq_fb529326a8de

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (u : (𝓞 K)ˣ) : u ∈ Units.torsion K := by
  rw [Units.mem_torsion]
  intro w
  rw [place_apply hK σ hσ]
  have h := abs_norm_eq hK σ hσ (u : K)
  rw [← Rat.cast_abs, Units.norm K u, Rat.cast_one] at h
  have h0 : 0 ≤ ‖σ (u : K)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖σ (u : K)‖ - 1), sq_nonneg (‖σ (u : K)‖ + 1)]
end GroundTheory.Heights₂.Theta.projectiveLineClassData

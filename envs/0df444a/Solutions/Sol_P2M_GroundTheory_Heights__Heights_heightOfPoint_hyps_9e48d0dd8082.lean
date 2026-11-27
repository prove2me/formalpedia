-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_heightOfPoint_hyps_9e48d0dd8082
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:11:46.554926+00:00
-- url     : https://prove2.me/submissions/63e2214c-fd05-4e17-b245-1a39cfacceec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratPointVec_apply_6946ec36e89e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    Submodule.span (𝓞 ℚ) (Set.range (Pi.basisFun (𝓞 ℚ) (Fin 2))) = ⊤ ∧ ratPointVec ≠ 0 ∧
      ratPointVec (Pi.basisFun (𝓞 ℚ) (Fin 2) 0) ≠ 0 := by
  have h1 : ratPointVec (Pi.single 0 1) = 1 := by
    simp [ratPointVec_apply]
  have h0 : ratPointVec (Pi.basisFun (𝓞 ℚ) (Fin 2) 0) = 1 := by
    rw [Pi.basisFun_apply]; exact h1
  refine ⟨(Pi.basisFun (𝓞 ℚ) (Fin 2)).span_eq, fun h ↦ ?_, by rw [h0]; exact one_ne_zero⟩
  have := congrArg (fun f : DualVec ℚ (Fin 2 → 𝓞 ℚ) ℚ ↦ f (Pi.basisFun (𝓞 ℚ) (Fin 2) 0)) h
  simp only [h0, LinearMap.zero_apply] at this
  exact one_ne_zero this
end GroundTheory.Heights₂.Heights

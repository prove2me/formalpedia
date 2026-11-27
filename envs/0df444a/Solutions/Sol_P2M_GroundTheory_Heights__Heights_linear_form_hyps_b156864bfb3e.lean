-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linear_form_hyps_b156864bfb3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:11:04.902447+00:00
-- url     : https://prove2.me/submissions/8fff3fee-4551-4393-b5a7-77ce86445d5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw

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
    ((X 0 : MvPolynomial (Fin 1) ℂ) ≠ 0 ∧ (X 0 : MvPolynomial (Fin 1) ℂ).IsHomogeneous 1 ∧
      eval (Pi.single 0 1) (X 0 : MvPolynomial (Fin 1) ℂ) ≠ 0) ∧
    ((X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 ∧ (X 0 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 ∧
      eval (Pi.single 0 1) (X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0) :=
  ⟨⟨X_ne_zero _, isHomogeneous_X _ _, by simp⟩, ⟨X_ne_zero _, isHomogeneous_X _ _, by simp⟩⟩
end GroundTheory.Heights₂.Heights

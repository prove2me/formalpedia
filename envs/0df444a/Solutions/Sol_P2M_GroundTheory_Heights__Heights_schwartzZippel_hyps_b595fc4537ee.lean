-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_schwartzZippel_hyps_b595fc4537ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:11:01.897847+00:00
-- url     : https://prove2.me/submissions/8bcb100f-f303-46b7-ae0f-da3e1f90decb

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
    (X 0 : MvPolynomial (Fin 2) ℤ) ≠ 0 ∧ ∀ i, (X 0 : MvPolynomial (Fin 2) ℤ).degreeOf i ≤ 1 := by
  refine ⟨X_ne_zero _, fun i ↦ ?_⟩
  rw [degreeOf_X]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights

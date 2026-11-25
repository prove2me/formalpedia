-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeDimComponent_proof_3c289e5b675c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:03.123186+00:00
-- url     : https://prove2.me/submissions/f7e3195e-5137-4bc0-bb30-4fbce7c9e9e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeDimComponent_proof_closed_0c228e09f176

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
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights
namespace ConeDimComponent
theorem _root_.solution (_h₁ : MinimalPrimeHomog.Statement) : ConeDimComponent.Statement :=
  ConeDimComponent.proof_closed
end ConeDimComponent
end GroundTheory.Heights₂.Heights

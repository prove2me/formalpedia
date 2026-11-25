-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_hypotheses_inhabited_d43ed208c544
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:13.663188+00:00
-- url     : https://prove2.me/submissions/5b49dade-32e1-4759-9163-764a4b1f787a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder

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
open LineChowForm
namespace GroundTheory.Heights₂.Heights
namespace LengthFiniteAlgebra
theorem _root_.solution :
    IsLocalRing ℤ_[2] ∧ IsNoetherianRing ℤ_[2] ∧ Module.Finite ℤ_[2] ℤ_[2] :=
  ⟨inferInstance, inferInstance, inferInstance⟩
end LengthFiniteAlgebra
end GroundTheory.Heights₂.Heights

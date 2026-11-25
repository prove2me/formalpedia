-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FGNullstellensatz_hypotheses_inhabited_7f04cfac262e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:23.691505+00:00
-- url     : https://prove2.me/submissions/f543d87f-79c6-4c43-9092-5c0c25702e40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements

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
namespace GroundTheory.Heights₂.Heights
namespace FGNullstellensatz
theorem _root_.solution : IsReduced ℚ ∧ Algebra.FiniteType ℚ ℚ :=
  ⟨inferInstance, inferInstance⟩
end FGNullstellensatz
end GroundTheory.Heights₂.Heights

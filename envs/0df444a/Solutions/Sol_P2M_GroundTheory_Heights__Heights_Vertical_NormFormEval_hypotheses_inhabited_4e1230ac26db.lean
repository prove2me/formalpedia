-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormEval_hypotheses_inhabited_4e1230ac26db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:24.208157+00:00
-- url     : https://prove2.me/submissions/293ffced-75c3-465d-be15-b0d858012b0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace NormFormEval
theorem _root_.solution : Module.Free ℚ ℚ ∧ Module.Finite ℚ ℚ :=
  ⟨inferInstance, inferInstance⟩
end NormFormEval
end GroundTheory.Heights₂.Heights.Vertical

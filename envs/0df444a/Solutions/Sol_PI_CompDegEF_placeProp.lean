-- Prove2me | solution 1 for PI.CompDegEF.placeProp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:32.328149+00:00
-- url     : https://prove2.me/submissions/a05b3ea8-e4a9-41a1-bca7-e80106d5427a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution : PlaceProp := by
  intro l _ E _ _ φ
  refine ⟨plOf φ, natCast_mem_plIdeal φ, fun x => ⟨norm_le_one_of_integer φ x, Iff.rfl⟩⟩
end PI.CompDegEF

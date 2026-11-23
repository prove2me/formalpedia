-- Prove2me | solution 1 for PI.CompAtExist.muV_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:52.229063+00:00
-- url     : https://prove2.me/submissions/709b7b7c-f6e5-41e9-a6f2-efad33be38bb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
namespace PI.CompAtExist
theorem _root_.solution (s : SplitPlace L) (k : L) : muV s k = Valued.v (s.i k) := rfl
end PI.CompAtExist

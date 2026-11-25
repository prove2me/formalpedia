-- Prove2me | solution 1 for PI.LocalEndW.norm_le_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:50:51.254713+00:00
-- url     : https://prove2.me/submissions/2d946b1c-6f73-41ff-9432-f97cd2ec98ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Filter Topology
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocalEndW
theorem _root_.solution (a : v.adicCompletionIntegers F) : ‖(a : v.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr a.2
end PI.LocalEndW

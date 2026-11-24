-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kmuIncl_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:12.897586+00:00
-- url     : https://prove2.me/submissions/7049e127-346d-4e8e-8b65-286d139505ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KmuInclDenseRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (x : Kmu l) : ‖kmuIncl l x‖ = ‖x‖ := rfl
end ReciprocityTheory.ChartRestriction.L1

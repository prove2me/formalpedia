-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_cutProjK_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:14.469909+00:00
-- url     : https://prove2.me/submissions/d8c485a0-4d52-42a5-9817-907ac580d98d

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (x : Fin r → K) : cutProjK K r e x = projGe K r e x := rfl
end ReciprocityTheory.MultiplicativeHeights

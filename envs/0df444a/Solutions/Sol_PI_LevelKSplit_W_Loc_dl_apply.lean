-- Prove2me | solution 1 for PI.LevelKSplit.W.Loc.dl_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:11.671806+00:00
-- url     : https://prove2.me/submissions/67a54754-a103-4ebb-82ba-53d29d9b732e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Loc
open Submodule
variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}
namespace PI.LevelKSplit.W.Loc
theorem _root_.solution (c y : Fin n → B) : dl c y = c ⬝ᵥ y := rfl
end PI.LevelKSplit.W.Loc

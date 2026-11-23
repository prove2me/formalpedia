-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.pV_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:01.479544+00:00
-- url     : https://prove2.me/submissions/6c308aef-690d-4ac4-9c19-2e31e16b834d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (D : Dat A n r) (x : n → A) : pV D x = x - D.pX x - D.pXv x := rfl
end PI.LevelKSplit.W.NCL

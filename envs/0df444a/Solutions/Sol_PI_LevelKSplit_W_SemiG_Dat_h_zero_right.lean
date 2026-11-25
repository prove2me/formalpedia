-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:57.638681+00:00
-- url     : https://prove2.me/submissions/d84aa38b-2b45-4081-be02-fc7029cd0cde

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable (D : Dat A n r)
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (x : n → A) : D.h x 0 = 0 := (D.hL x).map_zero
end PI.LevelKSplit.W.SemiG.Dat

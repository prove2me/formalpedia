-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:16.970483+00:00
-- url     : https://prove2.me/submissions/0415e52a-d9b2-4563-9fa1-317bc6fa8cb4

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
theorem _root_.solution (x y y' : n → A) : D.h x (y - y') = D.h x y - D.h x y' := (D.hL x).map_sub y y'
end PI.LevelKSplit.W.SemiG.Dat

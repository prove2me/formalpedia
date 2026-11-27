-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:32.987358+00:00
-- url     : https://prove2.me/submissions/20c3e9e4-bf0e-4ad8-9d2a-0ef82de3117c

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
theorem _root_.solution (x x' y : n → A) : D.h (x - x') y = D.h x y - D.h x' y := by
  simp only [h, hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
end PI.LevelKSplit.W.SemiG.Dat

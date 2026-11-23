-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.pX_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:19.540604+00:00
-- url     : https://prove2.me/submissions/36792493-0815-441b-814a-87821fa57a21

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_hL_apply

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
variable {D}
variable (D)
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (v : n → A) : D.pX v = ∑ a, D.h (D.f a) v • D.e a := by
  simp [pX, LinearMap.sum_apply, hL_apply]
end PI.LevelKSplit.W.SemiG.Dat

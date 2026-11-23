-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:55.206629+00:00
-- url     : https://prove2.me/submissions/4c8f9b95-99c6-45b5-9291-9376d4f9730e

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
variable {D}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) (x y : n → A) : D.h y x = D.σA (D.h x y) := by
  simp only [h, hform, map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end PI.LevelKSplit.W.SemiG.Dat

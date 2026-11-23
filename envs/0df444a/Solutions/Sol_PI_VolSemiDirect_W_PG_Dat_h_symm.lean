-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:41.302178+00:00
-- url     : https://prove2.me/submissions/3396a6ca-095d-4077-b2af-1412c3353e18

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable (D : Dat A n r)
variable {D}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) (x y : n → A) : D.h y x = D.σA (D.h x y) := by
  simp only [h, hform, map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end PI.VolSemiDirect.W.PG.Dat

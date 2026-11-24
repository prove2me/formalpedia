-- Prove2me | solution 1 for PositivityTheory.Mix.PlaneOK.symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:37.045877+00:00
-- url     : https://prove2.me/submissions/5c9dff09-fd86-4b5a-97de-ee29af07780f

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Mix
open Matrix
variable {R : Type} [CommRing R] {n k : ℕ}
variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}
open PositivityTheory.Mix.PlaneOK
variable {ε : R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin k) R} (h : PlaneOK c J ε x y ι)
include h
namespace PositivityTheory.Mix.PlaneOK
theorem _root_.solution (u v) : bf c J v u = ε * c (bf c J u v) := by
  simp only [bf, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, h.cc]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h.herm]
  linear_combination (-(v i * J i j * c (u j))) * h.ee
end PositivityTheory.Mix.PlaneOK

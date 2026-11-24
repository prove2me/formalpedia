-- Prove2me | solution 1 for PositivityTheory.Mix.PlaneOK.lev_i
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:03.759658+00:00
-- url     : https://prove2.me/submissions/abca13cb-a181-408e-8083-a1635eb7df4b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_apply

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
theorem _root_.solution (t s : R) (z) : lev c J ε x y t s *ᵥ (ι *ᵥ z) = ι *ᵥ z := by
  rw [lev_apply, h.iy, h.ix]
  simp
end PositivityTheory.Mix.PlaneOK

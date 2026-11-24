-- Prove2me | solution 1 for PositivityTheory.Mix.PlaneOK.levi_element_fixes_first_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:05.595821+00:00
-- url     : https://prove2.me/submissions/af9daec9-a4f7-458d-a8e3-bd42743f4313

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
theorem _root_.solution (t s : R) : lev c J ε x y t s *ᵥ x = t • x := by
  rw [lev_apply, h.xy, h.xx]
  simp only [mul_one, mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]
  abel
end PositivityTheory.Mix.PlaneOK

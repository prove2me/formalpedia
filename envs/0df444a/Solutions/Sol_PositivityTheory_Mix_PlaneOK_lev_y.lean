-- Prove2me | solution 1 for PositivityTheory.Mix.PlaneOK.lev_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:04.723085+00:00
-- url     : https://prove2.me/submissions/9c191479-883c-47df-b0a2-26e307b36864

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_yx
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
theorem _root_.solution (t s : R) : lev c J ε x y t s *ᵥ y = s • y := by
  rw [lev_apply, h.yy, h.yx]
  have e : (s - 1) * ε * ε = s - 1 := by rw [mul_assoc, h.ee, mul_one]
  rw [e]
  simp only [mul_zero, zero_smul, add_zero]
  rw [sub_smul, one_smul]
  abel
end PositivityTheory.Mix.PlaneOK

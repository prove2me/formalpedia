-- Prove2me | solution 1 for PositivityTheory.Mix.PlaneOK.lev_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:28:04.498666+00:00
-- url     : https://prove2.me/submissions/68448c71-279d-4001-a82f-65c10c0f3620

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_ext
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_levi_element_fixes_first_vector
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_y
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_i

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
theorem _root_.solution {t t' s s' : R} (h1 : t * t' = 1) (h2 : s * s' = 1) : lev c J ε x y t s * lev c J ε x y t' s' = 1 := by
  apply h.ext
  · rw [← mulVec_mulVec, h.levi_element_fixes_first_vector, mulVec_smul, h.levi_element_fixes_first_vector, smul_smul, mul_comm, h1, one_smul, one_mulVec]
  · rw [← mulVec_mulVec, h.lev_y, mulVec_smul, h.lev_y, smul_smul, mul_comm, h2, one_smul, one_mulVec]
  · intro z
    rw [← mulVec_mulVec, h.lev_i, h.lev_i, one_mulVec]
end PositivityTheory.Mix.PlaneOK

-- Prove2me | solution 1 for PositivityTheory.Mix.PlaneOK.lev_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:19.073278+00:00
-- url     : https://prove2.me/submissions/386fd69d-8b82-461c-a217-c93f981b0af9

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
import Theorems.Thm_PositivityTheory_Mix_bf_add_l
import Theorems.Thm_PositivityTheory_Mix_bf_smul_l
import Theorems.Thm_PositivityTheory_Mix_bf_add_r
import Theorems.Thm_PositivityTheory_Mix_bf_smul_r
import Theorems.Thm_PositivityTheory_Mix_bf_mulVec
import Theorems.Thm_PositivityTheory_Mix_bf_single
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_yx
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_xi
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_yi
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
theorem _root_.solution {t s : R} (h1 : t * c s = 1) : (lev c J ε x y t s)ᵀ * J * (lev c J ε x y t s).map c = J := by
  have hcs : s * c t = 1 := by
    have e := congrArg c h1
    rw [map_mul, h.cc, map_one] at e
    rw [mul_comm]
    exact e
  have key : ∀ u v, bf c J (lev c J ε x y t s *ᵥ u) (lev c J ε x y t s *ᵥ v) = bf c J u v := by
    intro u v
    obtain ⟨a, b, z, rfl⟩ := h.span u
    obtain ⟨a', b', z', rfl⟩ := h.span v
    simp only [mulVec_add, mulVec_smul, h.levi_element_fixes_first_vector, h.lev_y, h.lev_i, bf_add_l, bf_add_r, bf_smul_l, bf_smul_r,
      h.xx, h.yy, h.xy, h.yx, h.ix, h.iy, h.xi, h.yi, map_mul, smul_smul]
    linear_combination (a * c b') * h1 + (b * c a' * ε) * hcs
  ext i j
  have e := key (Pi.single i 1) (Pi.single j 1)
  rw [bf_mulVec, bf_single, bf_single] at e
  exact e
end PositivityTheory.Mix.PlaneOK

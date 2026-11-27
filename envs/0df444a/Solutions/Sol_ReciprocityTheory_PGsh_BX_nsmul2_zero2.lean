-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmul2_zero2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:15.017916+00:00
-- url     : https://prove2.me/submissions/b8fc2113-b723-476f-a3a8-277d208a3e0b

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreSnd_nsmul_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution (x : B.G R) (n : ℕ) : HEq (B.nsmul2 (B.zero2 x) n) (B.zero2 x) := by
  have h := B.fibreSnd_nsmul_mk (B.zero2 x) n
  have h0 : (B.S2mk (B.zero2 x)) = 0 := rfl
  rw [h0, nsmul_zero] at h
  exact (Sigma.ext_iff.1 h.symm).2
end ReciprocityTheory.PGsh.BX

-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmul2_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:51:18.665128+00:00
-- url     : https://prove2.me/submissions/492ff1ab-0906-4eff-b9be-6bcccb224f1a

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreSnd_nsmul_mk
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreSnd_nsmul_smul

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
theorem _root_.solution {x y : B.G R} (l : (R : Type u)ˣ) (u : B.P R x y) (n : ℕ) :
    B.nsmul2 (B.smul l u) n = B.smul (l ^ n) (B.nsmul2 u n) := by
  have h := B.fibreSnd_nsmul_smul l (B.S2mk u) n
  have e : B.SecondaryComponentScale l (B.S2mk u) = B.S2mk (B.smul l u) := rfl
  rw [e, fibreSnd_nsmul_mk, fibreSnd_nsmul_mk] at h
  exact eq_of_heq (Sigma.ext_iff.1 h).2
end ReciprocityTheory.PGsh.BX

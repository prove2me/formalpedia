-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmul1_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:15.535408+00:00
-- url     : https://prove2.me/submissions/71db7bb3-1525-444e-b62e-8b761a257f30

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreFst_nsmul_mk
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreFst_nsmul_smul

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
    B.nsmul1 (B.smul l u) n = B.smul (l ^ n) (B.nsmul1 u n) := by
  have h := B.fibreFst_nsmul_smul l (B.S1mk u) n
  have e : B.PrimaryComponentScale l (B.S1mk u) = B.S1mk (B.smul l u) := rfl
  rw [e, fibreFst_nsmul_mk, fibreFst_nsmul_mk] at h
  exact eq_of_heq (Sigma.ext_iff.1 h).2
end ReciprocityTheory.PGsh.BX

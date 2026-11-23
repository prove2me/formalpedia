-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmul_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:43.909868+00:00
-- url     : https://prove2.me/submissions/02ee5342-b750-4eea-b78a-ce453454c50e

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreFst_nsmul_mk

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
theorem _root_.solution {x y : B.G R} (u : B.P R x y) (m n : ℕ) :
    B.nsmul2 (B.nsmul1 u m) n = B.nsmul1 (B.nsmul2 u n) m := by
  have h := (B.S1n2 y n).map_nsmul m (B.S1mk u)
  rw [fibreFst_nsmul_mk] at h
  have h' : (B.S1mk (B.nsmul2 (B.nsmul1 u m) n)) =
      m • (B.S1mk (B.nsmul2 u n)) := h
  rw [fibreFst_nsmul_mk] at h'
  exact eq_of_heq (Sigma.ext_iff.1 h').2
end ReciprocityTheory.PGsh.BX

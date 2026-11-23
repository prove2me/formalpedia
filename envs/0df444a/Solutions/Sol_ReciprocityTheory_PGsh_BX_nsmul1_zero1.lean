-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmul1_zero1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:52.958687+00:00
-- url     : https://prove2.me/submissions/436d1c1e-8374-43dc-85a7-3aa25311bcd7

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
theorem _root_.solution (y : B.G R) (n : ℕ) : HEq (B.nsmul1 (B.zero1 y) n) (B.zero1 y) := by
  have h := B.fibreFst_nsmul_mk (B.zero1 y) n
  have h0 : (B.S1mk (B.zero1 y)) = 0 := rfl
  rw [h0, nsmul_zero] at h
  exact (Sigma.ext_iff.1 h.symm).2
end ReciprocityTheory.PGsh.BX

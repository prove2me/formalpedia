-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.sw_nsmul1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:30.80029+00:00
-- url     : https://prove2.me/submissions/ae652efe-349e-472e-8cd1-e45556e35c8b

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_zero1
import Theorems.Thm_ReciprocityTheory_PGsh_BX_swap_castFst

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
theorem _root_.solution {x y : B.G R} (u : B.P R x y) (n : ℕ) :
    B.sw (B.nsmul1 u n) = B.nsmul2 (B.sw u) n := by
  induction n with
  | zero => exact (B.swap_castFst _ _).trans (by rw [sw_zero1]; rfl)
  | succ n ih => exact (B.swap_castFst _ _).trans (by rw [B.swap_addFst, ih]; rfl)
end ReciprocityTheory.PGsh.BX

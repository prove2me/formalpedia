-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.fibreSnd_nsmul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:18.353551+00:00
-- url     : https://prove2.me/submissions/fa73a7e2-e6c4-45c7-9811-cf2f0d8d5570

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst

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
theorem _root_.solution {x : B.G R} (l : (R : Type u)ˣ) (a : B.S2 R x) (n : ℕ) :
    n • B.SecondaryComponentScale l a = B.SecondaryComponentScale (l ^ n) (n • a) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, pow_zero, S2smul_one]
  | succ n ih => rw [succ_nsmul, succ_nsmul, ih, S2smul_add, pow_succ]
end ReciprocityTheory.PGsh.BX

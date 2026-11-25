-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.fibreFst_nsmul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:14:39.178217+00:00
-- url     : https://prove2.me/submissions/befb8657-a1cf-48b2-861b-a5be890be57e

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
theorem _root_.solution {y : B.G R} (l : (R : Type u)ˣ) (a : B.S1 R y) (n : ℕ) :
    n • B.PrimaryComponentScale l a = B.PrimaryComponentScale (l ^ n) (n • a) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, pow_zero, S1smul_one]
  | succ n ih => rw [succ_nsmul, succ_nsmul, ih, S1smul_add, pow_succ]
end ReciprocityTheory.PGsh.BX

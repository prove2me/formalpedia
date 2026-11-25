-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.isUnit_det_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:42:11.34362+00:00
-- url     : https://prove2.me/submissions/65303411-5b82-4b1a-b9ac-fd932f565f8a

import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) R).det := by
  have h := Matrix.det_permutation (R := R) σ
  simp only [Equiv.Perm.permMatrix] at h
  rw [h]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
end ReciprocityTheory.PGsh.Up.Smith

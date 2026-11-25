-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.det_blockOne_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:45.336482+00:00
-- url     : https://prove2.me/submissions/bb9edcc3-2105-4d61-a3d9-b9f7084b8784

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
theorem _root_.solution {N : ℕ} (P : Matrix (Fin N) (Fin N) R) : (bd1 P).det = P.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [blockOne_zero_zero_alt, blockOne_zero_succ_alt, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one,
    Fin.val_zero, pow_zero, one_mul]
  all_goals congr 1
end ReciprocityTheory.PGsh.Up.Smith

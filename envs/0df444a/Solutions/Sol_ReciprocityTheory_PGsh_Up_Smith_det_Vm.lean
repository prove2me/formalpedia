-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.det_Vm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:44:02.146018+00:00
-- url     : https://prove2.me/submissions/18fb1656-5532-4978-9c01-c9367e8dd551

import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : (Vm j0 s).det = 1 := by
  rw [Matrix.det_succ_column (Vm j0 s) j0, Finset.sum_eq_single j0]
  · have hsub : (Vm j0 s).submatrix j0.succAbove j0.succAbove = 1 := by
      ext k l
      simp only [Matrix.submatrix_apply, Vm, Matrix.of_apply, Fin.succAbove_ne, if_false,
        sub_zero, Matrix.one_apply, (Fin.succAbove_right_injective).eq_iff]
    rw [hsub, Matrix.det_one]
    simp [Vm, ← two_mul, pow_mul]
  · intro k _ hk
    simp [Vm, hk]
  · intro h; exact absurd (Finset.mem_univ _) h
end ReciprocityTheory.PGsh.Up.Smith

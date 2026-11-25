-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.mul_Vm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:10.924481+00:00
-- url     : https://prove2.me/submissions/a11dd950-e403-4725-bfe5-38516ace70b6

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
theorem _root_.solution {m N : ℕ} (X : Matrix (Fin m) (Fin (N + 1)) R) (j0 : Fin (N + 1))
    (s : Fin (N + 1) → R) (i : Fin m) (l : Fin (N + 1)) :
    (X * Vm j0 s) i l = if l = j0 then X i j0 else X i l - s l * X i j0 := by
  classical
  simp only [Matrix.mul_apply, Vm, Matrix.of_apply]
  by_cases hl : l = j0
  · simp [hl]
  · simp only [hl, if_false, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
end ReciprocityTheory.PGsh.Up.Smith

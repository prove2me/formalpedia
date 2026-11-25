-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.det_re_le_mul_prod_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:34:21.342542+00:00
-- url     : https://prove2.me/submissions/ed112478-33ae-4ba0-a0ab-5d6894e5462d

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_fin_blocks
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_hadamard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      ∏ j : Fin b, (M (Fin.natAdd a j) (Fin.natAdd a j)).re := by
  have h1 := gramSt_fin_blocks hM
  have h2 := gramSt_hadamard (hM.submatrix (e := Fin.natAdd a) (Fin.natAdd_injective b a))
  have h0 : 0 ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re :=
    (Complex.pos_iff.mp (hM.submatrix (Fin.castAdd_injective a b)).det_pos).1.le
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h0)
end ReciprocityTheory.GeometryOfNumbersTheory

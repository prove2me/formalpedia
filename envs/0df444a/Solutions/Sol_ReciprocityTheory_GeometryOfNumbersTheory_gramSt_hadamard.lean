-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.gramSt_hadamard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:20:24.737324+00:00
-- url     : https://prove2.me/submissions/48282818-38f3-441b-ab74-42e2a149c3ef

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_fin_blocks

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
theorem _root_.solution {k : ℕ} {D : Matrix (Fin k) (Fin k) ℂ} (hD : D.PosDef) :
    D.det.re ≤ ∏ j : Fin k, (D j j).re := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := gramSt_fin_blocks (a := k) (b := 1) hD
    have h2 := ih (hD.submatrix (Fin.castAdd_injective k 1))
    have h3 : (D.submatrix (Fin.natAdd k) (Fin.natAdd k : Fin 1 → Fin (k + 1))).det =
        D (Fin.last k) (Fin.last k) := by
      rw [det_unique]; rfl
    have h4 : 0 ≤ (D (Fin.last k) (Fin.last k)).re := (Complex.pos_iff.mp hD.diag_pos).1.le
    rw [h3] at h1
    rw [Fin.prod_univ_castSucc]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 h4)
end ReciprocityTheory.GeometryOfNumbersTheory

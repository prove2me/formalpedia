-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.gramSt_fin_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:52:16.961289+00:00
-- url     : https://prove2.me/submissions/27b0fc44-789f-4046-9529-320d3eab4853

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_fischer

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
theorem _root_.solution {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ} (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).det.re := by
  have hE : M.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (M.submatrix (Fin.castAdd b) (Fin.castAdd b))
        (M.submatrix (Fin.castAdd b) (Fin.natAdd a))
        (M.submatrix (Fin.natAdd a) (Fin.castAdd b))
        (M.submatrix (Fin.natAdd a) (Fin.natAdd a)) := by
    ext (i | i) (j | j) <;> simp
  have hP : (M.submatrix finSumFinEquiv finSumFinEquiv).PosDef :=
    hM.submatrix finSumFinEquiv.injective
  rw [hE] at hP
  have := gramSt_fischer hP
  rwa [← hE, det_submatrix_equiv_self] at this
end ReciprocityTheory.GeometryOfNumbersTheory

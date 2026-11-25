-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_one_mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:30.128846+00:00
-- url     : https://prove2.me/submissions/36555bf7-34af-43c2-9ee1-9e08ff2477c3

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_mul_swap
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_one_gramPolyMinor_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    (cf 1 (Gm N hd m hm v) * Zm N m hm v) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have k := zMat_mul_swap N v (Fin.castLE hm a) (Fin.castLE hm b)
  simp only [Zm, submatrix_apply, coeffMatrix_one_gramPolyMinor_apply]
  linear_combination (hd (Fin.castLE hm a) : ℂ) * k
end ReciprocityTheory.AnForm.P

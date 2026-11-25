-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.conjTranspose_mul_coeffMatrix_one_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:38.906319+00:00
-- url     : https://prove2.me/submissions/ba872b6d-af81-4a44-b43b-a7b8e34250de

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
    ((Zm N m hm v)ᴴ * cf 1 (Gm N hd m hm v)) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have k := zMat_mul_swap N v (Fin.castLE hm a) (Fin.castLE hm b)
  have k' : star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
      star (zMat N v (Fin.castLE hm a) (Fin.castLE hm b)) = 0 := by
    rw [← star_mul, k, star_zero]
  simp only [conjTranspose_apply, Zm, submatrix_apply, coeffMatrix_one_gramPolyMinor_apply]
  linear_combination (hd (Fin.castLE hm a) : ℂ) * k'
end ReciprocityTheory.AnForm.P

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_two_reducedGramPolyMinor_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:28.254131+00:00
-- url     : https://prove2.me/submissions/63ea9757-cc0e-4bae-869f-43b9b7080cc1

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_zero
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_one
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_two
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_two_gramPoly_diag
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_unipotentLine
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_one_unipotentLine
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_two_unipotentLine
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_gramPolyMinor
import Theorems.Thm_ReciprocityTheory_AnForm_P_conjTranspose_mul_coeffMatrix_one_diag
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_one_mul_diag
import Theorems.Thm_ReciprocityTheory_AnForm_P_conjTranspose_mul_diagonal_mul_diag

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
    cf 2 (Gn N hd m hm v) a a =
      ∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  have e : cf 2 (Gn N hd m hm v) = cf 2 (Gm N hd m hm v) -
      (Zm N m hm v)ᴴ * cf 1 (Gm N hd m hm v) - cf 1 (Gm N hd m hm v) * Zm N m hm v +
      (Zm N m hm v)ᴴ * cf 0 (Gm N hd m hm v) * Zm N m hm v := by
    simp only [Gn, cf_mul_zero, cf_mul_one, cf_mul_two, coeffMatrix_zero_unipotentLine, coeffMatrix_one_unipotentLine, coeffMatrix_two_unipotentLine]
    noncomm_ring
  rw [e, coeffMatrix_zero_gramPolyMinor, Matrix.add_apply, Matrix.sub_apply, Matrix.sub_apply, conjTranspose_mul_coeffMatrix_one_diag, coeffMatrix_one_mul_diag, conjTranspose_mul_diagonal_mul_diag]
  have h2 : cf 2 (Gm N hd m hm v) a a = cf 2 (gP N hd v) (Fin.castLE hm a) (Fin.castLE hm a) :=
    rfl
  rw [h2, coeffMatrix_two_gramPoly_diag]
  ring
end ReciprocityTheory.AnForm.P

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.cf_cpP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:42.502808+00:00
-- url     : https://prove2.me/submissions/a4849b0d-ec8e-4b07-8e17-29812b75439d

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeff_X_pow_mul_C
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_apply


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
theorem _root_.solution (N n : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    cf n (cpP N A) = if n < N then ((n.factorial : ℂ)⁻¹) • A ^ n else 0 := by
  ext i j
  simp only [cpP, cf_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    finsetSum_coeff, coeff_X_pow_mul_C]
  rw [Finset.sum_ite_eq]
  by_cases h : n < N <;> simp [h]
end ReciprocityTheory.AnForm.P

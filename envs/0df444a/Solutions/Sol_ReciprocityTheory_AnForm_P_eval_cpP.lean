-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.eval_cpP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:31.561126+00:00
-- url     : https://prove2.me/submissions/9cf3faa7-1536-45c8-9194-5343139d6959

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB

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
theorem _root_.solution (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) :
    (cpP N A).map (eval t) = ∑ k ∈ Finset.range N, (t ^ k * ((k.factorial : ℂ)⁻¹)) • A ^ k := by
  ext i j
  simp only [cpP, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← coe_evalRingHom, map_sum]
  simp [mul_assoc]
end ReciprocityTheory.AnForm.P

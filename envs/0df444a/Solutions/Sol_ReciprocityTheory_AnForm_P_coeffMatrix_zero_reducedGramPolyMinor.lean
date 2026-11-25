-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_zero_reducedGramPolyMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:36.876085+00:00
-- url     : https://prove2.me/submissions/9764f06e-89ed-4f13-bcf6-12f41008032e

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_zero
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_unipotentLine
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_gramPolyMinor

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
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    cf 0 (Gn N hd m hm v) = diagonal fun a => (hd (Fin.castLE hm a) : ℂ) := by
  rw [Gn, cf_mul_zero, cf_mul_zero, coeffMatrix_zero_unipotentLine, coeffMatrix_zero_unipotentLine, Matrix.one_mul, Matrix.mul_one, coeffMatrix_zero_gramPolyMinor]
end ReciprocityTheory.AnForm.P

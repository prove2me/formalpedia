-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.det_gramPolyMinor_coeff_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:11.935197+00:00
-- url     : https://prove2.me/submissions/31b86cc9-5c0c-45cc-96f8-f70ee3a94114

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_det_Gn
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_reducedGramPolyMinor
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_one_reducedGramPolyMinor
import Theorems.Thm_ReciprocityTheory_AnForm_P_det_coeff_zero_one_of_coeffMatrix_one


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
    (Gm N hd m hm v).det.coeff 0 = ((∏ a : Fin m, hd (Fin.castLE hm a) : ℝ) : ℂ) ∧
      (Gm N hd m hm v).det.coeff 1 = 0 := by
  obtain ⟨h0, h1⟩ := det_coeff_zero_one_of_coeffMatrix_one (Gn N hd m hm v) (coeffMatrix_one_reducedGramPolyMinor N hd m hm v)
  rw [det_Gn] at h0 h1
  rw [h0, coeffMatrix_zero_reducedGramPolyMinor, det_diagonal, Complex.ofReal_prod]
  exact ⟨rfl, h1⟩
end ReciprocityTheory.AnForm.P

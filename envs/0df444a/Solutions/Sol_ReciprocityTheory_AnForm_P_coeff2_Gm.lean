-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeff2_Gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:19.170137+00:00
-- url     : https://prove2.me/submissions/0b305f2f-e8eb-4d4f-b5c1-9bd8657c962e

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_det_Gn
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_reducedGramPolyMinor
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_one_reducedGramPolyMinor
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_two_reducedGramPolyMinor_apply
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeff2_det_of


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
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N)
    (v : Pairs N → ℂ) :
    (Gm N hd m hm v).det.coeff 2 = (∏ a : Fin m, (hd (Fin.castLE hm a) : ℂ)) *
      ∑ a : Fin m, ((hd (Fin.castLE hm a) : ℂ))⁻¹ *
        (∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
        ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
          ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a))) := by
  rw [← det_Gn, coeff2_det_of (Gn N hd m hm v) (fun a => (hd (Fin.castLE hm a) : ℂ))
    (fun a => by exact_mod_cast hd0 _) (coeffMatrix_zero_reducedGramPolyMinor N hd m hm v) (coeffMatrix_one_reducedGramPolyMinor N hd m hm v)]
  simp only [coeffMatrix_two_reducedGramPolyMinor_apply]
end ReciprocityTheory.AnForm.P

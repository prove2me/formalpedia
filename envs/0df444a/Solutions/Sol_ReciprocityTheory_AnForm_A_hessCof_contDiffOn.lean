-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessCof_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:43.956613+00:00
-- url     : https://prove2.me/submissions/82cc312d-b130-4286-aeff-b51efe199d0d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_hessCof_multilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (U : Set (Fin (n + 1) → ℂ))
    (hU : IsOpen U) (m : ℕ) (hφ : ∀ i, ContDiffOn ℝ (m + 2) (φ i) U) (j k : Fin (n + 1)) :
    ContDiffOn ℝ m (fun y => hessCof φ y j k) U := by
  obtain ⟨G, hG⟩ := exists_hessCof_multilinear n j k
  have h2 : ∀ i, ContDiffOn ℝ m (fun y => fderiv ℝ (fderiv ℝ (φ i)) y) U := fun i =>
    ((hφ i).fderiv_of_isOpen (m := ((m + 1 : ℕ) : WithTop ℕ∞)) hU
      (by exact_mod_cast (show m + 1 + 1 ≤ m + 2 by omega))).fderiv_of_isOpen hU
      (by exact_mod_cast (le_refl (m + 1)))
  have hc : ContDiffOn ℝ m (fun y => G (fun i => fderiv ℝ (fderiv ℝ (φ i)) y)) U :=
    G.contDiff.comp_contDiffOn (contDiffOn_pi.2 h2)
  have hfun : (fun y => hessCof φ y j k) = fun y => G (fun i => fderiv ℝ (fderiv ℝ (φ i)) y) :=
    funext fun y => hG φ y
  rw [hfun]
  exact hc
end ReciprocityTheory.AnForm.A

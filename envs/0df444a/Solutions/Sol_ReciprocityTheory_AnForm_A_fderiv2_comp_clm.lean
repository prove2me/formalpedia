-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fderiv2_comp_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:08.823981+00:00
-- url     : https://prove2.me/submissions/741b5b7d-7637-4962-82d2-817181757d48

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → ℝ) (P : F →L[ℝ] E) (hg : ContDiff ℝ 2 g)
    (z a b : F) :
    fderiv ℝ (fderiv ℝ (g ∘ P)) z a b = fderiv ℝ (fderiv ℝ g) (P z) (P a) (P b) := by
  have h1 := iteratedFDeriv_two_apply (𝕜 := ℝ) (g ∘ P) z ![a, b]
  have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) g (P z) ![P a, P b]
  rw [P.iteratedFDeriv_comp_right hg z le_rfl] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  rw [← h1, ← h2]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i; fin_cases i <;> rfl
end ReciprocityTheory.AnForm.A

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:16.837948+00:00
-- url     : https://prove2.me/submissions/a5b20efd-ada1-4607-9f26-d3b1bb4217f9

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
theorem _root_.solution {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {m : ℕ} (hφ : ContDiffOn ℝ (m + 2) φ U) (i j : Fin D) :
    ContDiffOn ℝ m (fun z => hessC φ z i j) U := by
  have h1 : ContDiffOn ℝ (m + 1) (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_cast)
  have h2 : ContDiffOn ℝ m (fderiv ℝ (fderiv ℝ φ)) U := h1.fderiv_of_isOpen hU le_rfl
  have hH : ∀ a b : Fin D → ℂ, ContDiffOn ℝ m (fun z => fderiv ℝ (fderiv ℝ φ) z a b) U :=
    fun a b => (h2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hC : ∀ g : (Fin D → ℂ) → ℝ, ContDiffOn ℝ m g U → ContDiffOn ℝ m (fun z => (g z : ℂ)) U :=
    fun g hg => Complex.ofRealCLM.contDiff.comp_contDiffOn hg
  simp only [hessC]
  refine ContDiffOn.div_const (ContDiffOn.add (hC _ ((hH _ _).add (hH _ _)))
    (contDiffOn_const.mul (hC _ ((hH _ _).sub (hH _ _))))) _
end ReciprocityTheory.AnForm.A

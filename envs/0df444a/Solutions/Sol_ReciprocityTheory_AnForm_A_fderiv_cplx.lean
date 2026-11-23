-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fderiv_cplx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:51.77693+00:00
-- url     : https://prove2.me/submissions/991fc948-f233-4e48-a977-58f815d36047

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    fderiv ℝ (cplx v) z = Complex.ofRealCLM.comp (fderiv ℝ v z) := by
  by_cases h : DifferentiableAt ℝ v z
  · exact (Complex.ofRealCLM.hasFDerivAt.comp z h.hasFDerivAt).fderiv
  · have h' : ¬ DifferentiableAt ℝ (cplx v) z := by
      intro hc
      apply h
      have : v = fun y => Complex.reCLM (cplx v y) := by funext y; simp [cplx]
      rw [this]
      exact Complex.reCLM.differentiableAt.comp z hc
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']
    simp
end ReciprocityTheory.AnForm.A

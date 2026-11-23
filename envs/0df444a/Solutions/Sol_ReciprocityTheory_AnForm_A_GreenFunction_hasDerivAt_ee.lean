-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.hasDerivAt_ee
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:39.18024+00:00
-- url     : https://prove2.me/submissions/902b44e1-8028-4ba0-b27d-01984a3616cd

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A.GreenFunction
theorem _root_.solution (θ : ℝ) : HasDerivAt ee (Complex.I * ee θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).ofReal_comp).add
    (((Real.hasDerivAt_sin θ).ofReal_comp).mul_const Complex.I)
  have e : Complex.I * ee θ = ((-Real.sin θ : ℝ) : ℂ) + (Real.cos θ : ℂ) * Complex.I := by
    simp only [ee, Complex.ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * Complex.I_sq
  rw [e]; exact h
end ReciprocityTheory.AnForm.A.GreenFunction

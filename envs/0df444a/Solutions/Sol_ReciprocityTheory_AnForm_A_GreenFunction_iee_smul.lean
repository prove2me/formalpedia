-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.iee_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:28.662772+00:00
-- url     : https://prove2.me/submissions/60bba9aa-45f3-40a1-a3be-2455cdba5593

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
theorem _root_.solution (θ : ℝ) :
    Complex.I * ee θ = (-Real.sin θ) • (1 : ℂ) + Real.cos θ • Complex.I := by
  simp only [ee, Complex.real_smul, Complex.ofReal_neg]
  linear_combination (Real.sin θ : ℂ) * Complex.I_sq
end ReciprocityTheory.AnForm.A.GreenFunction

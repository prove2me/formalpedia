-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.ee_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:26.193721+00:00
-- url     : https://prove2.me/submissions/3aa3b2a3-0ee3-49f9-8a8f-04922038440c

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
theorem _root_.solution (θ : ℝ) : ee θ = Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
  simp [ee, Complex.real_smul]
end ReciprocityTheory.AnForm.A.GreenFunction

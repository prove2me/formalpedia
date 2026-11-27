-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.hasDerivAt_ang
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:24.659319+00:00
-- url     : https://prove2.me/submissions/e3fae38d-d239-461d-80fa-9213c52db4c0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_ee

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
variable {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ)
include hu
namespace ReciprocityTheory.AnForm.A.GreenFunction
theorem _root_.solution (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => u (a + r • ee θ))
      (fderiv ℝ u (a + r • ee θ) (r • (Complex.I * ee θ))) θ := by
  have hp : HasDerivAt (fun θ : ℝ => a + r • ee θ) (r • (Complex.I * ee θ)) θ :=
    ((hasDerivAt_ee θ).const_smul r).const_add a
  exact ((hu.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt θ hp
end ReciprocityTheory.AnForm.A.GreenFunction

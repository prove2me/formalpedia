-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:06.01034+00:00
-- url     : https://prove2.me/submissions/ea94e6fd-dd8c-474f-a131-481909f5193e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_lap_eq_rot

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
theorem _root_.solution (u : ℂ → ℝ) (a : ℂ) (r θ : ℝ) :
    r * Real.log r * Δ u (a + r • ee θ) = Arad u a θ r + AngularPart u a r θ := by
  rw [lap_eq_rot u _ θ]; simp only [Arad, AngularPart]; ring
end ReciprocityTheory.AnForm.A.GreenFunction

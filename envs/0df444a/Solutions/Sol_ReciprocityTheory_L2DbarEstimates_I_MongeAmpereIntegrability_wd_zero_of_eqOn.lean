-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.wd_zero_of_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:21.321236+00:00
-- url     : https://prove2.me/submissions/010ac8d6-831e-4eb0-861a-a58902e0f844

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
theorem _root_.solution {Z : Set (V n)} (hZ : IsOpen Z) {g : V n → ℂ}
    (h : ∀ w ∈ Z, g w = 0) (j : Fin n) {y : V n} (hy : y ∈ Z) :
    wd n j g y = 0 ∧ wdb n j g y = 0 := by
  have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℂ) := Filter.eventually_of_mem (hZ.mem_nhds hy) fun w hw => h w hw
  have hd : fderiv ℝ g y = 0 := by
    rw [hev.fderiv_eq]; simp
  constructor <;> simp [wd, wdb, hd]
end ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability

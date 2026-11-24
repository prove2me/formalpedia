-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:37.364882+00:00
-- url     : https://prove2.me/submissions/c448fdcc-01c9-4aad-9198-fecfcca0031d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {σ W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (s : Finset ι) (c : ι → ℂ) (F : ι → W → ℂ)
    (hF : ∀ i ∈ s, ∀ k : ℕ, ContDiff ℂ k (F i)) (x : W) :
    polyDeriv P u (fun w => ∑ i ∈ s, c i * F i w) x = ∑ i ∈ s, c i * polyDeriv P u (F i) x := by
  unfold polyDeriv
  have hD : ∀ N : ℕ, iteratedFDeriv ℂ N (fun w => ∑ i ∈ s, c i * F i w) x =
      ∑ i ∈ s, c i • iteratedFDeriv ℂ N (F i) x := by
    intro N
    show iteratedFDeriv ℂ N (fun w => ∑ i ∈ s, c i • F i w) x = _
    rw [iteratedFDeriv_sum (fun i hi => (hF i hi N).const_smul (c i)), Finset.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact iteratedFDeriv_const_smul_apply (a := c i) (hF i hi N).contDiffAt
  simp only [hD, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.I2

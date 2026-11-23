-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity.flow_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:46.082805+00:00
-- url     : https://prove2.me/submissions/75636418-394c-4b07-8cc2-999170aa2b2e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (la : Wt X.Ψ r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
theorem _root_.solution (ξ : Fin r → E) (x : Frame X.Ψ r) :
    Differentiable ℂ (fun s : X.Ψ → ℂ => X.flow ξ s x) := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  intro s
  simp only [Data.flow, Matrix.mul_apply, Data.flowMat, Matrix.of_apply, mat]
  refine DifferentiableAt.fun_sum fun k _ => ?_
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_mul
  exact (differentiable_apply τ) s
end ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity

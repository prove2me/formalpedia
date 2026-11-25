-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.scaledPeriod_mem_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:40.026413+00:00
-- url     : https://prove2.me/submissions/f7fe412e-ba78-4450-a0c4-b31eb0b5a064

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PeriodLatticeMembership_basicPeriod_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
theorem _root_.solution (la la' : Wt X.Ψ r) (j : Fin (Fintype.card X.Ψ)) : omc X la la' j ∈ X.periods la := by
  show ((X.chiOrd la' * X.chiOrd (la + la') : ℕ) : ℝ) • om1 X la j ∈ X.periods la
  simp only [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ (basicPeriod_mem X la j) _
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership

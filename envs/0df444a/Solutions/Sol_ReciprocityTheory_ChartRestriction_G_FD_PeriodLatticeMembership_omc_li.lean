-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.omc_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:11:32.646055+00:00
-- url     : https://prove2.me/submissions/70ba4da3-08fe-4789-95a3-631ed40cf2fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PeriodLatticeMembership_basicPeriod_linearIndependent

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
theorem _root_.solution (la la' : Wt X.Ψ r) : LinearIndependent ℝ (omc X la la') := by
  have hC : ((X.chiOrd la' * X.chiOrd (la + la') : ℕ) : ℝ) ≠ 0 := by
    have h1 : 0 < X.chiOrd la' := (X.χ_fin la').choose_spec.1
    have h2 : 0 < X.chiOrd (la + la') := (X.χ_fin (la + la')).choose_spec.1
    have h3 : 0 < X.chiOrd la' * X.chiOrd (la + la') := Nat.mul_pos h1 h2
    exact_mod_cast h3.ne'
  have h := (basicPeriod_linearIndependent X la).units_smul (fun _ => Units.mk0 _ hC)
  convert h using 1
  funext j
  first
    | rfl
    | simp [omc, Units.smul_def]
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership

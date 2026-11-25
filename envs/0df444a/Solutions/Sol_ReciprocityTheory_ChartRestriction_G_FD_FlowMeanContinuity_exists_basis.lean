-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:29:26.099929+00:00
-- url     : https://prove2.me/submissions/7c65405d-b0d3-40ed-995e-a90358b378fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealEmbeddingCharacters_perL_rank


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
theorem _root_.solution : ∃ ω : Module.Basis (Fin (Fintype.card X.Ψ)) ℝ (X.Ψ → ℝ),
    Submodule.span ℤ (Set.range ω) = perL X la := by
  classical
  let b := Module.Free.chooseBasis ℤ (perL X la)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (perL X la)) = Fintype.card X.Ψ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, perL_rank]
  refine ⟨(b.ofZLatticeBasis ℝ (perL X la)).reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity

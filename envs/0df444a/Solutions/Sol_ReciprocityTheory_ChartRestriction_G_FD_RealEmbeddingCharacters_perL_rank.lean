-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.perL_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:46.679958+00:00
-- url     : https://prove2.me/submissions/0ee26699-48c1-469a-a89e-81fb75ed90c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (la : Wt X.Ψ r)
namespace ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
theorem _root_.solution : Module.finrank ℤ (perL X la) = Fintype.card X.Ψ := by
  rw [ZLattice.rank ℝ (perL X la)]
  exact Module.finrank_fintype_fun_eq_card ℝ
end ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters

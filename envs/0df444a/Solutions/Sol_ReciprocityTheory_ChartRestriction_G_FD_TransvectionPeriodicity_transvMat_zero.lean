-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.transvMat_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:00:13.176579+00:00
-- url     : https://prove2.me/submissions/a5839e84-2e73-43b8-aed7-ba53654b0041

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : transvMat G ξ 0 = 1 := by
  ext a b
  simp [transvMat, Matrix.one_apply]
end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity

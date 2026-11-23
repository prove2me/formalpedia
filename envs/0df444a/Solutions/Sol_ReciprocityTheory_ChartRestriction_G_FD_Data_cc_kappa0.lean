-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.cc_kappa0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:15.633643+00:00
-- url     : https://prove2.me/submissions/46758a19-e2ca-43ed-a5d7-a936d7febdc3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution : cc X.κ0 = -X.κ0 := by
  have hx : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  rcases X.κ0_xi with h | h <;> rw [h] <;> simp only [cc, map_mul, map_neg, map_ofNat, hx] <;> ring
end ReciprocityTheory.ChartRestriction.G.FD.Data

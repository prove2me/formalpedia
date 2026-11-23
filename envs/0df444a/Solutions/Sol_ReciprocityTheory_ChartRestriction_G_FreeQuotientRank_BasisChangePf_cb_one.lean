-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:33.440429+00:00
-- url     : https://prove2.me/submissions/73bf5902-5be2-44c0-b962-9e9272fb2e7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf
open MvPolynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf
theorem _root_.solution : CB (1 : MvPolynomial ι K) 1 := by
  classical
  intro μ
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf

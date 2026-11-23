-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:04.222541+00:00
-- url     : https://prove2.me/submissions/1d189536-8def-4c84-821e-01681d3ac800

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
theorem _root_.solution {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a ∈ s, CB (g a) c) : CB (∑ a ∈ s, g a) c := by
  classical
  intro μ
  rw [MvPolynomial.coeff_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc (fun a ha => h a ha μ)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf

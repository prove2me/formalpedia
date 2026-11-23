-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:04.191029+00:00
-- url     : https://prove2.me/submissions/011b530b-5afe-48b2-9304-c73c6b221bfc

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
theorem _root_.solution {Q R : MvPolynomial ι K} {c d : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (hR : CB R d)
    (hd : 0 ≤ d) : CB (Q * R) (c * d) := by
  classical
  intro μ
  rw [MvPolynomial.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) (fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hQ _) (hR _) (norm_nonneg _) hc
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf

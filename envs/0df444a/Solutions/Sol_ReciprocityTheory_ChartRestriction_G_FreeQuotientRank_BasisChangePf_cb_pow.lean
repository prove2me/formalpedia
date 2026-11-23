-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:57.699719+00:00
-- url     : https://prove2.me/submissions/45d7b054-9696-438c-b9e4-140d10e0d01d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_one

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
theorem _root_.solution {Q : MvPolynomial ι K} {c : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (n : ℕ) : CB (Q ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact cb_mul (pow_nonneg hc n) ih hQ hc
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf

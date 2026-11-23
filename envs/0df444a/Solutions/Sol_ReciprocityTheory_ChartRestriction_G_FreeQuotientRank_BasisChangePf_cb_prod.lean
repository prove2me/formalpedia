-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:44.724809+00:00
-- url     : https://prove2.me/submissions/cb0dbae8-eea8-4626-818e-b5abb226a30f

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
theorem _root_.solution {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) (c : α → ℝ) (hc : ∀ a, 0 ≤ c a)
    (h : ∀ a ∈ s, CB (g a) (c a)) : CB (∏ a ∈ s, g a) (∏ a ∈ s, c a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact cb_mul (hc a) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
      (Finset.prod_nonneg fun b _ => hc b)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf

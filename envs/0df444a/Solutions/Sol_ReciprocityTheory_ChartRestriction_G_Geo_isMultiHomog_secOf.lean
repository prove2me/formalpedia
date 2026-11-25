-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_secOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:15:56.506369+00:00
-- url     : https://prove2.me/submissions/5b775bdb-4991-4eb0-9569-8106f57d6c4f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_blockDeg_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_secOf_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (i : ∀ k, ι k) (b : K → ℕ) : IsMultiHomog (secOf i b) b := by
  classical
  intro m hm k
  rw [secOf_eq, MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_comm]
  simp only [blockDeg_single]
  simp
end ReciprocityTheory.ChartRestriction.G.Geo

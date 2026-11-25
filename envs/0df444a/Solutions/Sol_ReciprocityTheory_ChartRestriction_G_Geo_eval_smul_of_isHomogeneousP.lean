-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_isHomogeneousP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:09.616801+00:00
-- url     : https://prove2.me/submissions/f84b992d-8ba4-4352-8fcd-c394bac49d0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet

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
open MvPolynomial
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {R : Type*} [CommRing R] {φ : MvPolynomial ι R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : ι → R) : eval (c • z) φ = c ^ d * eval z φ := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hφ (mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
end ReciprocityTheory.ChartRestriction.G.Geo

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.aeval_sumElim_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:41.736682+00:00
-- url     : https://prove2.me/submissions/1fac06a1-a4cd-45cb-92d3-d7748c46bf6e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_inr_eq_of_weight_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (k0 : K)
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {S : Type*} [CommRing S] [Algebra ℚ S] {r : ℕ}
    {H : MvPolynomial (Fin r ⊕ {k // k ≠ k0}) ℚ} {δ : K →₀ ℕ}
    (hH : IsWeightedHomogeneous (sWt k0 r) H δ) {n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (hn0 : n0 ∈ H.support) (a : Fin r → S) (b : {k // k ≠ k0} → S) :
    aeval (Sum.elim a b) H = (∏ k', b k' ^ n0 (Sum.inr k')) * aeval (Sum.elim a 1) H := by
  classical
  have hw : ∀ n ∈ H.support, ∀ k', n (Sum.inr k') = n0 (Sum.inr k') := fun n hn k' =>
    inr_eq_of_weight_eq k0
      ((hH (mem_support_iff.mp hn)).trans (hH (mem_support_iff.mp hn0)).symm) k'
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  have hp : ∏ k', b k' ^ n (Sum.inr k') = ∏ k', b k' ^ n0 (Sum.inr k') :=
    Finset.prod_congr rfl fun k' _ => by rw [hw n hn k']
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_pow, Finset.prod_const_one, mul_one, hp]
  ring
end ReciprocityTheory.ChartRestriction.G.Geo

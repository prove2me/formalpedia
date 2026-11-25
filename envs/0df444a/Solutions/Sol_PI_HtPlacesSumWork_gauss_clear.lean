-- Prove2me | solution 1 for PI.HtPlacesSumWork.gauss_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:30.351436+00:00
-- url     : https://prove2.me/submissions/33ac6829-32ab-45b4-88c8-6ed4be076fbf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_GaussMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
namespace PI.HtPlacesSumWork
theorem _root_.solution (p : KTp K D N) :
    ∃ x : OT K D N, ∃ n : 𝓞 K, n ≠ 0 ∧
      OTtoKT K D N x = OTtoKT K D N (MvPolynomial.C n) * p := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (p.support.image fun v => p.coeff v)
  have hint_r : ∀ v ∈ p.support, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (b : 𝓞 K) • p.coeff v := by
    intro v hv
    exact RingHom.mem_rangeS.mp (hb _ (Finset.mem_image_of_mem _ hv))
  choose! g hg using hint_r
  refine ⟨∑ v ∈ p.support, MvPolynomial.monomial v (g v), b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.T0.OTtoKT, map_sum, MvPolynomial.map_C]
  conv_rhs => rw [p.as_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.C_mul_monomial, hg v hv, Algebra.smul_def]
end PI.HtPlacesSumWork

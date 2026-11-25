-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_aeval_mul_of_homog_224f703392af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:10.371082+00:00
-- url     : https://prove2.me/submissions/6f8cbc0b-7bea-4792-934e-1cf73da7ec91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointMultChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointMultiplicity
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointMultiplicity
theorem _root_.solution [Fintype K] [∀ k, Fintype (ι k)] {S : Type*} [CommRing S] [Algebra ℤ S] (r : (Σ k, ι k) → S) (t : K → S) {f : MRing ι}
    {d : K → ℕ} (hf : IsMultiHomog f d) :
    aeval (fun p => r p * t p.1) f = aeval r f * ∏ k, t k ^ d k := by
  classical
  rw [f.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  dsimp only
  rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
end GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointMultiplicity

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_monomial_mul_43714485359b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:21.795022+00:00
-- url     : https://prove2.me/submissions/b9492423-9734-4a0d-9763-f9efaf0d1bb4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeIndepSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep
theorem _root_.solution (e : (Σ k, ι k) →₀ ℕ) {p : MRingOver S ι}
    (h : monomial e (1 : S) * p = 0) : p = 0 := by
  ext d
  have := congrArg (coeff (e + d)) h
  rw [coeff_monomial_mul, one_mul, coeff_zero] at this
  rw [this, coeff_zero]
end GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep

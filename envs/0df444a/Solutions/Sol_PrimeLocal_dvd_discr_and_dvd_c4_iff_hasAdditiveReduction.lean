-- Prove2me | solution 1 for PrimeLocal.dvd_discr_and_dvd_c4_iff_hasAdditiveReduction
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:03:03.300215+00:00
-- url     : https://prove2.me/submissions/7f11eb16-eeed-44eb-9ba8-7726d4ae6d7a

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
theorem _root_.solution (W : WeierstrassCurve ℤ) (q : ℕ) [Fact q.Prime] [WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))] : (W.map (Int.castRingHom ℚ_[q])).HasAdditiveReduction ℤ_[q] ↔ ((q : ℤ) ∣ W.Δ ∧ (q : ℤ) ∣ W.c₄) := by
  have h (z : ℤ) :
      IsDedekindDomain.HeightOneSpectrum.valuation ℚ_[q]
        (IsDiscreteValuationRing.maximalIdeal ℤ_[q]) (z : ℚ_[q]) < 1 ↔ (q : ℤ) ∣ z := by
    have hz := IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (K := ℚ_[q]) (IsDiscreteValuationRing.maximalIdeal ℤ_[q]) (z : ℤ_[q])
    change _ ↔ (z : ℤ_[q]) ∈ IsLocalRing.maximalIdeal ℤ_[q] at hz
    simpa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
      ← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_int_lt_one_iff_dvd] using hz
  have hm : IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q])) := inferInstance
  rw [hasAdditiveReduction_iff]
  simpa [WeierstrassCurve.map_Δ, WeierstrassCurve.map_c₄, h, hm]

end PrimeLocal

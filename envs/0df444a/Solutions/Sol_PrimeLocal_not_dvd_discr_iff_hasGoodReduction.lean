-- Prove2me | solution 1 for PrimeLocal.not_dvd_discr_iff_hasGoodReduction
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:03:04.283521+00:00
-- url     : https://prove2.me/submissions/98f5ac82-6c60-4beb-8641-907c02e8ec26

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
private theorem dvd_discr_and_dvd_c4_iff_hasAdditiveReduction (W : WeierstrassCurve ℤ) (q : ℕ) [Fact q.Prime] [WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))] : (W.map (Int.castRingHom ℚ_[q])).HasAdditiveReduction ℤ_[q] ↔ ((q : ℤ) ∣ W.Δ ∧ (q : ℤ) ∣ W.c₄) := by
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

/-- Good reduction of a minimal integral equation is detected by its discriminant. -/
theorem _root_.solution (W : WeierstrassCurve ℤ) (q : ℕ) [Fact q.Prime] [WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))] :
    (W.map (Int.castRingHom ℚ_[q])).HasGoodReduction ℤ_[q] ↔ ¬ (q : ℤ) ∣ W.Δ := by
  have h (z : ℤ) :
      IsDedekindDomain.HeightOneSpectrum.valuation ℚ_[q]
        (IsDiscreteValuationRing.maximalIdeal ℤ_[q]) (z : ℚ_[q]) < 1 ↔ (q : ℤ) ∣ z := by
    have hz := IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (K := ℚ_[q]) (IsDiscreteValuationRing.maximalIdeal ℤ_[q]) (z : ℤ_[q])
    change _ ↔ (z : ℤ_[q]) ∈ IsLocalRing.maximalIdeal ℤ_[q] at hz
    simpa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
      ← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_int_lt_one_iff_dvd] using hz
  have hm : IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q])) := inferInstance
  have hle := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (K := ℚ_[q]) (IsDiscreteValuationRing.maximalIdeal ℤ_[q]) (W.Δ : ℤ_[q])
  rw [hasGoodReduction_iff]
  simp only [hm, true_and, WeierstrassCurve.map_Δ, map_intCast]
  rw [← h W.Δ, not_lt]
  exact ⟨fun e => e.ge, fun le => le_antisymm hle le⟩

end PrimeLocal

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Monic_dvd_of_dvd_C_pow_mul_pow_15cde19839a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:30.48477+00:00
-- url     : https://prove2.me/submissions/51a0a8eb-b3be-4cc2-ae4d-ecd0ce82f584

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace Monic
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] {m u v h : Polynomial R} {c : R}
    (hm : m.Monic) (hc : c ≠ 0) (huv : u * m + v * Polynomial.derivative m = Polynomial.C c) {e N : ℕ}
    (hN : N ≠ 0) (hd : m ∣ Polynomial.C c ^ e * h ^ N) : m ∣ h := by
  have hf : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R (FractionRing R)
  have hfc : algebraMap R (FractionRing R) c ≠ 0 :=
    (map_ne_zero_iff _ hf).2 hc
  have hsep : (m.map (algebraMap R (FractionRing R))).Separable := by
    rw [Polynomial.separable_def']
    refine ⟨Polynomial.C (algebraMap R (FractionRing R) c)⁻¹ * u.map (algebraMap R (FractionRing R)),
      Polynomial.C (algebraMap R (FractionRing R) c)⁻¹ * v.map (algebraMap R (FractionRing R)), ?_⟩
    have h1 := congrArg (Polynomial.map (algebraMap R (FractionRing R))) huv
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at h1
    rw [mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul, inv_mul_cancel₀ hfc, Polynomial.C_1]
  have hd' : m.map (algebraMap R (FractionRing R)) ∣
      Polynomial.C (algebraMap R (FractionRing R) c) ^ e * (h.map (algebraMap R (FractionRing R))) ^ N := by
    have := Polynomial.map_dvd (algebraMap R (FractionRing R)) hd
    rwa [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_C] at this
  have hu : IsUnit (Polynomial.C (algebraMap R (FractionRing R) c) ^ e) :=
    (Polynomial.isUnit_C.2 (Ne.isUnit hfc)).pow e
  have h2 : m.map (algebraMap R (FractionRing R)) ∣ h.map (algebraMap R (FractionRing R)) :=
    (hsep.squarefree.dvd_pow_iff_dvd hN).1 ((hu.dvd_mul_left).1 hd')
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd (hm.map _), ← Polynomial.map_modByMonic _ hm] at h2
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hm]
  exact Polynomial.map_injective _ hf (by rw [h2, Polynomial.map_zero])
end Monic
end GroundTheory.Heights₂.Heights

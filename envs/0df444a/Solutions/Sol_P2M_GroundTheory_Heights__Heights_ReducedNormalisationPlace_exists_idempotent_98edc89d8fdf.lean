-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_exists_idempotent_98edc89d8fdf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:32:33.638801+00:00
-- url     : https://prove2.me/submissions/f6c07ccd-19dc-40cd-8e56-9eca514775e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PReducedNormalisationPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_eq_zero_iff_d0d39b2f0e93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_fracMap_unit_ede7a277c87b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_isIntegral_mul_of_fracMap_31178a133ad5


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
open MvPolynomial ComplexSets MinimalPrimePlace
noncomputable section
open GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
theorem _root_.solution [IsNoetherianRing A] [IsReduced A] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    ∃ e : integralClosure A (FractionRing A), ∀ (B : Type) [CommRing B] [IsDomain B] (π : A →+* B),
      Function.Surjective π → ∀ hker : RingHom.ker π = p,
        fracMap π (by rw [hker]; exact hp) e = 1 ∧
          ∀ z, fracMap π (by rw [hker]; exact hp) z = 0 → (e : FractionRing A) * z = 0 := by
  have := hp.1.1
  have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes A := by rwa [Ideal.mk_ker]
  obtain ⟨e, he1, hek, -⟩ := exists_fracMap_unit (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective hk
  have he : IsIntegral A e := by
    simpa using isIntegral_mul_of_fracMap _ Ideal.Quotient.mk_surjective hk (x := 1) he1 hek
      (by rw [map_one]; exact isIntegral_one)
  refine ⟨⟨e, he⟩, fun B _ _ π _ hker ↦ ⟨?_, fun z hz ↦ hek z ?_⟩⟩
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    rw [← sub_eq_zero, ← map_one (fracMap π hπ), ← map_sub,
      fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]), map_sub, he1, map_one,
      sub_self]
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    exact (fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]) z).1 hz
end GroundTheory.Heights₂.Heights.ReducedNormalisationPlace

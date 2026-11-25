-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sliceCMUnmixed_local_c3dc3ab32cc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:41.421833+00:00
-- url     : https://prove2.me/submissions/1d91d5ef-bb47-4832-addd-8c8f0dc964c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCMUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMQuotientUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceCMUnmixed

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
open MvPolynomial Matrix ComplexSets IsLocalRing
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : CMQuotientUnmixed.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (m : Ideal R) [m.IsPrime] {d : ℕ} (J : Ideal R) (ℓ : Fin d → R) (hℓ : ∀ i, ℓ i ∈ m)
    (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (π : Localization.AtPrime m →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J.map (algebraMap R (Localization.AtPrime m)))
    (hB : ringKrullDim B = (d + 1 : ℕ))
    (hS : ringKrullDim (Localization.AtPrime m ⧸
      (J ⊔ Ideal.span (Set.range ℓ)).map (algebraMap R (Localization.AtPrime m))) = (1 : ℕ)) :
    ∀ P ∈ associatedPrimes R (R ⧸ (J ⊔ Ideal.span (Set.range ℓ))), P ≤ m →
      P ∈ (J ⊔ Ideal.span (Set.range ℓ)).minimalPrimes ∧ P ≠ m := by
  intro P hP hPm
  obtain ⟨I, hI⟩ : ∃ I, I = J ⊔ Ideal.span (Set.range ℓ) := ⟨_, rfl⟩
  rw [← hI] at hP hS ⊢
  have hJI : J ≤ I := hI ▸ le_sup_left
  let x : Fin d → B := fun i => π (algebraMap R (Localization.AtPrime m) (ℓ i))

  have hspan : Ideal.span (Set.range x) = (I.map (algebraMap R (Localization.AtPrime m))).map π := by
    rw [hI, Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker π).2 hker.ge, bot_sup_eq,
      Ideal.map_map, Ideal.map_span, ← Set.range_comp]
    rfl
  have hker_le : ∀ Q : Ideal R, J ≤ Q → RingHom.ker π ≤ Q.map (algebraMap R (Localization.AtPrime m)) :=
    fun Q hQ => hker ▸ Ideal.map_mono hQ
  have hcomap : ∀ Q : Ideal R, J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π =
        Q.map (algebraMap R (Localization.AtPrime m)) := fun Q hQ => by
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 (hker_le Q hQ)]

  have hdimx : ringKrullDim (B ⧸ Ideal.span (Set.range x)) = (1 : ℕ) := by
    let f : Localization.AtPrime m →+* B ⧸ Ideal.span (Set.range x) := (Ideal.Quotient.mk _).comp π
    have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
    have hkf : RingHom.ker f = I.map (algebraMap R (Localization.AtPrime m)) := by
      ext c
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap,
        hcomap I hJI]
    rw [← ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf),
      ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hkf), hS]
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => by
    have : IsLocalHom π := IsLocalHom.of_surjective π hπ
    exact map_nonunit π _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m (ℓ i)).2
      (hℓ i))
  have hsum : ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B := by
    rw [hdimx, hB, ← Nat.cast_add, Nat.add_comm]

  obtain ⟨hPp, y, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmemP : ∀ s, s ∈ P ↔ s * r ∈ I := fun s => by
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot,
      show s • Ideal.Quotient.mk I r = Ideal.Quotient.mk I (s * r) from rfl, Ideal.Quotient.eq_zero_iff_mem]
  have hIP : I ≤ P := fun s hs => (hmemP s).2 (I.mul_mem_right r hs)
  have hdisj : ∀ Q : Ideal R, Q ≤ m → Disjoint (m.primeCompl : Set R) Q :=
    fun Q hQ => Set.disjoint_left.2 fun u hu huQ => hu (hQ huQ)
  have hprime : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).IsPrime := fun Q hQ hQm hJQ => by
    have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) Q hQ (hdisj Q hQm)
    exact Ideal.map_isPrime_of_surjective hπ (hker_le Q hJQ)
  have hback : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      (((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π).comap
        (algebraMap R (Localization.AtPrime m)) = Q := fun Q hQ hQm hJQ => by
    rw [hcomap Q hJQ]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ hQ (hdisj Q hQm)
  obtain ⟨p, hp⟩ : ∃ p, p = (P.map (algebraMap R (Localization.AtPrime m))).map π := ⟨_, rfl⟩
  have hpP : p.IsPrime := hp ▸ hprime P hPp hPm (hJI.trans hIP)

  have hass : p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)) := by
    refine isAssociatedPrime_iff.2 ⟨hpP, Ideal.Quotient.mk _ (π (algebraMap R (Localization.AtPrime m) r)), ?_⟩
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
      show π a • Ideal.Quotient.mk (Ideal.span (Set.range x)) (π (algebraMap R (Localization.AtPrime m) r)) =
        Ideal.Quotient.mk _ (π (a * algebraMap R (Localization.AtPrime m) r)) by rw [map_mul]; rfl,
      Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap, ← Ideal.mem_comap, hcomap I hJI, hp,
      hcomap P (hJI.trans hIP)]
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl a
    rw [← IsLocalization.mk'_one (M := m.primeCompl) (Localization.AtPrime m) r, ← IsLocalization.mk'_mul,
      mul_one, IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
    simp_rw [hmemP, mul_assoc]
  obtain ⟨hmin, hdimp⟩ := h B d x hxm hsum p hass
  refine ⟨⟨⟨hPp, hIP⟩, fun Q ⟨hQp, hIQ⟩ hQP => ?_⟩, fun hPeq => ?_⟩
  · have hQm : Q ≤ m := hQP.trans hPm
    have hJQ : J ≤ Q := hJI.trans hIQ
    have h1 : Ideal.span (Set.range x) ≤ (Q.map (algebraMap R (Localization.AtPrime m))).map π := by
      rw [hspan]
      exact Ideal.map_mono (Ideal.map_mono hIQ)
    have h2 : (Q.map (algebraMap R (Localization.AtPrime m))).map π ≤ p :=
      hp ▸ Ideal.map_mono (Ideal.map_mono hQP)
    have h3 := hmin.2 ⟨hprime Q hQp hQm hJQ, h1⟩ h2
    rw [← hback P hPp hPm (hJI.trans hIP), ← hback Q hQp hQm hJQ, ← hp]
    exact Ideal.comap_mono (Ideal.comap_mono h3)
  · have hpmax : p.IsMaximal := by
      have := Ideal.map_eq_top_or_isMaximal_of_surjective π hπ
        (maximalIdeal.isMaximal (Localization.AtPrime m))
      rw [hPeq, Localization.AtPrime.map_eq_maximalIdeal] at hp
      rw [← hp] at this
      exact this.resolve_left hpP.ne_top
    let := Ideal.Quotient.field p
    have h0 : ringKrullDim (B ⧸ p) = 0 := ringKrullDim_eq_zero_of_field (B ⧸ p)
    rw [hdimp, hdimx] at h0
    exact absurd h0 (by simp)
end GroundTheory.Heights₂.Heights

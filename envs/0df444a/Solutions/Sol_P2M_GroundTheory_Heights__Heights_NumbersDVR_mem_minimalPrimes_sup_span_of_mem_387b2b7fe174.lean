-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_of_mem_387b2b7fe174
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:30.142314+00:00
-- url     : https://prove2.me/submissions/814de5c5-39f9-444e-a1f7-e63aa8aa894c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RelevantMinimalOfDivCycleNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {A : Type*} [CommRing A] [IsNoetherianRing A] {P H : Ideal A}
    [hP : P.IsPrime] {x y : A} (hH : H ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hy : y ∉ P)
    (hyH : y ∈ H) : H ∈ (P ⊔ Ideal.span {y}).minimalPrimes := by
  have : H.IsPrime := hH.1.1
  have hPH : P ≤ H := le_sup_left.trans hH.1.2
  obtain ⟨Q, hQ, hQH⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPH ((Ideal.span_singleton_le_iff_mem _).mpr hyH))
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hyQ : y ∈ Q := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
  suffices hQH' : Q = H by rw [← hQH']; exact hQ
  by_contra hne
  have hlt : Q < H := lt_of_le_of_ne hQH hne
  let φ := Ideal.Quotient.mk P
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hHm : (H.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hQm : (Q.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hcomap : ∀ I : Ideal A, P ≤ I → (I.map φ).comap φ = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI]
  have h_lt : Q.map φ < H.map φ := (Ideal.map_mono hlt.le).lt_of_not_ge fun h => hlt.not_ge (by
    simpa only [hcomap Q hPQ, hcomap H hPH] using Ideal.comap_mono (f := φ) h)
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hH
  have : (H.map φ).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime h_lt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h0' : Q.map φ ∈ (⊥ : Ideal (A ⧸ P)).minimalPrimes := h0
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at h0'
  have : φ y ∈ Q.map φ := Ideal.mem_map_of_mem φ hyQ
  rw [show Q.map φ = ⊥ from h0', Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact hy this
end GroundTheory.Heights₂.Heights.NumbersDVR

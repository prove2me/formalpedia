-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_KrullHeightOne_proof_77952fbc9c6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:59:53.316384+00:00
-- url     : https://prove2.me/submissions/dd9b7edb-65b6-4588-8b6a-ee0d62fafe37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsKrullHeightOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PKrullHeightOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_KrullHeightOne_exists_prime_colon_f4d9dec4bfc3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open Ideal
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace KrullHeightOne
theorem _root_.solution : KrullHeightOne.Statement := by
  intro A _ _ _ _ p q hpq
  obtain ⟨hq, hqp⟩ := hpq
  obtain ⟨a, P, hPp, hb, hP⟩ := KrullHeightOne.exists_prime_colon p q hqp
  have hqP : q ∈ P := (hP q).2 (dvd_mul_right q _)
  have hPbot : P ≠ ⊥ := fun h => hq (by rw [h, Ideal.mem_bot] at hqP; exact hqP)

  have hex : ∃ u ∈ P, ∃ w ∉ P, u * (a * p) = q * w := by
    by_contra hne
    have hne' : ∀ u ∈ P, ∀ w, u * (a * p) = q * w → w ∈ P := by
      intro u hu w huw
      by_contra hw
      exact hne ⟨u, hu, w, hw, huw⟩
    have hqK : algebraMap A (FractionRing A) q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hq
    let N : Submodule A (FractionRing A) := Submodule.map (Algebra.linearMap A (FractionRing A)) P
    have hN : N ≠ ⊥ := by
      intro h
      have : algebraMap A (FractionRing A) q ∈ N := Submodule.mem_map_of_mem hqP
      rw [h, Submodule.mem_bot] at this
      exact hqK this
    have hNfg : N.FG := (IsNoetherian.noetherian P).map _
    have hy : IsIntegral A (algebraMap A (FractionRing A) (a * p) / algebraMap A (FractionRing A) q) := by
      refine isIntegral_of_smul_mem_submodule N hN hNfg _ ?_
      intro n hn
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨w, hw⟩ := (hP x).1 hx
      have hwP : w ∈ P := hne' x hx w hw
      refine Submodule.mem_map.2 ⟨w, hwP, ?_⟩
      show algebraMap A (FractionRing A) w =
        algebraMap A (FractionRing A) (a * p) / algebraMap A (FractionRing A) q *
          algebraMap A (FractionRing A) x
      rw [div_mul_eq_mul_div, eq_div_iff hqK, ← map_mul, ← map_mul, mul_comm (a * p) x, hw,
        mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hy
    apply hb
    refine ⟨z, IsFractionRing.injective A (FractionRing A) ?_⟩
    rw [map_mul _ q z, hz]
    exact (mul_div_cancel₀ _ hqK).symm
  obtain ⟨u, hu, w, hw, huw⟩ := hex

  have hmin : P ∈ (Ideal.span {u}).minimalPrimes := by
    refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 hu⟩, ?_⟩
    rintro Q ⟨hQ, huQ⟩ hQP x hx
    obtain ⟨v, hv⟩ := (hP x).1 hx
    have h1 : x * w = u * v := by
      apply mul_left_cancel₀ hq
      linear_combination (-x) * huw + u * hv
    have h2 : x * w ∈ Q := by
      rw [h1]
      exact Q.mul_mem_right v ((Ideal.span_singleton_le_iff_mem _).1 huQ)
    rcases hQ.mem_or_mem h2 with h | h
    · exact h
    · exact absurd (hQP h) hw
  have : (Ideal.span {u}).IsPrincipal := ⟨⟨u, rfl⟩⟩
  have := hPp
  have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
  have hge : 1 ≤ P.height :=
    Order.one_le_iff_ne_zero.2 fun h => hPbot (Ideal.height_eq_zero_iff_eq_bot.1 h)
  refine ⟨P, hPp, le_antisymm hle hge, w, hw, u * a, P.mul_mem_right a hu, ?_⟩
  linear_combination -huw
end KrullHeightOne
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

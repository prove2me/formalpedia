-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_isPrime_between_not_mem_f98685f45555
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:14.276986+00:00
-- url     : https://prove2.me/submissions/e5f96952-2156-420c-a806-e89ffc227b44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_one_lt_height_map_17d807a61c21

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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
theorem _root_.solution [IsNoetherianRing R] {p q r : Ideal R} [p.IsPrime]
    [q.IsPrime] [r.IsPrime] (hpq : p < q) (hqr : q < r) {x : R} (hx : x ∉ p) :
    ∃ q' : Ideal R, q'.IsPrime ∧ p < q' ∧ q' < r ∧ x ∉ q' := by
  classical
  by_contra H
  push Not at H
  have hM : (p ⊔ Ideal.span {x}).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R _
  let s : Finset (Ideal R) := insert p (hM.toFinset.filter (· < r))
  have hprime : ∀ t ∈ s, t.IsPrime := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · infer_instance
    · exact (hM.mem_toFinset.1 (Finset.mem_filter.1 ht).1).isPrime
  have hlt : ∀ t ∈ s, t < r := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hpq.trans hqr
    · exact (Finset.mem_filter.1 ht).2
  have hnot : ¬ ((r : Set R) ⊆ ⋃ t ∈ (↑s : Set (Ideal R)), ((fun t : Ideal R => t) t : Set R)) := by
    intro h
    obtain ⟨t, ht, hrt⟩ :=
      (Ideal.subset_union_prime (f := fun t : Ideal R => t) p p
        (fun t ht _ _ => hprime t ht)).1 h
    exact (hlt t ht).not_ge hrt
  obtain ⟨y, hyr, hy⟩ := Set.not_subset.1 hnot
  simp only [Set.mem_iUnion, not_exists] at hy
  have hyp : y ∉ p := fun h => hy p (Finset.mem_coe.2 (Finset.mem_insert_self _ _)) h
  have hyt : ∀ t ∈ (p ⊔ Ideal.span {x}).minimalPrimes, t < r → y ∉ t := fun t ht htr h =>
    hy t (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hM.mem_toFinset.2 ht, htr⟩))) h
  have hle : p ⊔ Ideal.span {y} ≤ r :=
    sup_le (hpq.trans hqr).le (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  obtain ⟨t0, ht0, ht0r⟩ := Ideal.exists_minimalPrimes_le hle
  have : t0.IsPrime := ht0.isPrime
  have hKrull := Ideal.map_height_le_one_of_mem_minimalPrimes ht0
  have hyt0 : y ∈ t0 := ht0.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
  have hpt0 : p < t0 :=
    lt_of_le_of_ne (le_sup_left.trans ht0.1.2) fun h => hyp (by rw [h]; exact hyt0)
  have ht0r' : t0 < r := by
    refine lt_of_le_of_ne ht0r fun h => ?_
    have h2 := one_lt_height_map hpq hqr
    rw [← h] at h2
    exact absurd hKrull (not_le.2 h2)
  have hxt0 : x ∈ t0 := H t0 inferInstance hpt0 ht0r'
  have hle' : p ⊔ Ideal.span {x} ≤ t0 :=
    sup_le (le_sup_left.trans ht0.1.2) (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  obtain ⟨t', ht', ht't0⟩ := Ideal.exists_minimalPrimes_le hle'
  have : t'.IsPrime := ht'.isPrime
  have hxt' : x ∈ t' := ht'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  have hpt' : p < t' :=
    lt_of_le_of_ne (le_sup_left.trans ht'.1.2) fun h => hx (by rw [h]; exact hxt')
  have ht'eq : t' = t0 := by
    by_contra hne
    exact absurd hKrull (not_le.2 (one_lt_height_map hpt' (lt_of_le_of_ne ht't0 hne)))
  exact hyt t' ht' (ht'eq ▸ ht0r') (ht'eq ▸ hyt0)
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe

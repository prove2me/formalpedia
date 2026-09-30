-- Prove2me | solution 1 for TranscendenceTheory.isolated_component_differential_contact
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T17:32:24.512825+00:00
-- url     : https://prove2.me/submissions/f4c2088e-edc6-4d91-bcec-d340437e807e

import Definitions.Def_TranscendenceTheory_PrimeMultiplicityData
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.IsPrimary
import Theorems.Thm_TranscendenceTheory_differential_prime_localization
import Mathlib.Tactic

open TranscendenceTheory

theorem solution
    (R : Type*) [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (p : Ideal R) [p.IsPrime]
    (n : ℕ) (J : Fin n → Ideal R) (i : Fin n)
    (hother : ∀ j, j ≠ i → ¬ J j ≤ p) :
    ∃ s : R, s ∉ p ∧
      (∀ f ∈ J i, s * f ∈ ⨅ j, J j) ∧
      (⨅ j, J j).map (algebraMap R (Localization.AtPrime p)) =
        (J i).map (algebraMap R (Localization.AtPrime p)) ∧
      (∀ T : ℕ,
        (∀ f ∈ ⨅ j, J j, ∀ k ≤ T, (D^[k]) f ∈ p) ↔
        (∀ f ∈ J i, ∀ k ≤ T, (D^[k]) f ∈ p)) ∧
      ((J i).IsPrimary → (J i).radical = p →
        ((⨅ j, J j).map (algebraMap R (Localization.AtPrime p))).under R = J i) := by
  classical
  have hex : ∀ j : Fin n, ∃ a : R, (j ≠ i → a ∈ J j) ∧ a ∉ p := by
    intro j
    by_cases hji : j = i
    · exact ⟨1, fun h => False.elim (h hji), p.one_notMem⟩
    · have h := hother j hji
      change ¬ ∀ a, a ∈ J j → a ∈ p at h
      push Not at h
      obtain ⟨a, ha, hap⟩ := h
      exact ⟨a, fun _ => ha, hap⟩
  choose a ha using hex
  let s : R := ∏ j ∈ Finset.univ.erase i, a j
  have hs : s ∉ p := by
    intro h
    obtain ⟨j, _, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact (ha j).2 hj
  have hsep : ∀ f ∈ J i, s * f ∈ ⨅ j, J j := by
    intro f hf
    rw [Ideal.mem_iInf]
    intro j
    by_cases hji : j = i
    · subst j
      exact (J i).mul_mem_left s hf
    · exact (J j).mul_mem_right f
        ((J j).prod_mem (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) ((ha j).1 hji))
  have hmap : (⨅ j, J j).map (algebraMap R (Localization.AtPrime p)) =
      (J i).map (algebraMap R (Localization.AtPrime p)) := by
    apply le_antisymm (Ideal.map_mono (iInf_le J i))
    apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) (⨅ j, J j) f).mpr ⟨s, hs, hsep f hf⟩
  refine ⟨s, hs, hsep, hmap, ?_, ?_⟩
  · obtain ⟨d, _, hjet⟩ := differential_prime_localization R D p
    intro T
    rw [hjet (⨅ j, J j) T, hjet (J i) T, hmap]
  · intro hprimary hradical
    rw [hmap]
    apply IsLocalization.under_map_of_isPrimary_disjoint p.primeCompl
      (Localization.AtPrime p) hprimary
    apply Set.disjoint_left.mpr
    intro a hap haJ
    exact hap (hradical ▸ Ideal.le_radical haJ)

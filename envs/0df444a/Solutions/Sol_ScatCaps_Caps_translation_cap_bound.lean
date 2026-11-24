-- Prove2me | solution 1 for ScatCaps.Caps.translation_cap_bound
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:03:09.587312+00:00
-- url     : https://prove2.me/submissions/6dbb0cc0-e778-4832-83b2-fc45334e3241

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

open ScatCaps.Caps

theorem solution (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) (ht : 1 < t) {r : ℕ} (S : Set (Fin r → K))
    (hS : IsTranslationCap S) :
    S.ncard ^ 2 ≤ (2 ^ t) ^ r := by
  classical
  obtain ⟨hcap, G, hG⟩ := hS
  have memG : ∀ x, x ∈ S ↔ x ∈ G := fun x => by rw [← hG]; rfl
  have hω : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro ω _
      by_cases h0 : ω = 0
      · simp [h0]
      · simp [h ω h0]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hK] at h1
    have h3 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    have h4 : 2 ^ 2 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    omega
  obtain ⟨ω, hω0, hω1⟩ := hω
  have key : Set.InjOn (fun p : (Fin r → K) × (Fin r → K) => p.1 + ω • p.2) (S ×ˢ S) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨a', b'⟩ ⟨ha', hb'⟩ h
    simp only at h ha hb ha' hb'
    have hd : a - a' = ω • b' - ω • b := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm (ω • b')]
      exact h
    rw [← smul_sub] at hd
    by_cases hbb : b' - b = 0
    · have hb_eq : b = b' := (sub_eq_zero.mp hbb).symm
      have ha_eq : a = a' := by
        rw [hbb, smul_zero] at hd
        exact sub_eq_zero.mp hd
      rw [ha_eq, hb_eq]
    · exfalso
      set d := b' - b with hdd
      have hdG : d ∈ G := G.sub_mem ((memG _).mp hb') ((memG _).mp hb)
      have hωdG : ω • d ∈ G := by
        rw [← hd]
        exact G.sub_mem ((memG _).mp ha) ((memG _).mp ha')
      have hne : d ≠ ω • d := by
        intro h'
        apply hω1
        have h'' : (ω - 1) • d = 0 := by rw [sub_smul, one_smul, ← h', sub_self]
        rcases smul_eq_zero.mp h'' with h3 | h3
        · exact sub_eq_zero.mp h3
        · exact absurd h3 hbb
      apply hcap 0 ((memG _).mpr G.zero_mem) d ((memG _).mpr hdG) (ω • d) ((memG _).mpr hωdG)
        (fun h' => hbb h'.symm) (fun h' => smul_ne_zero hω0 hbb h'.symm) hne
      rw [collinear_iff_of_mem (Set.mem_insert _ _)]
      refine ⟨d, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨ω, by simp⟩
  have hcard := Set.ncard_le_ncard_of_injOn _ (fun p _ => Set.mem_univ (p.1 + ω • p.2)) key
    (Set.toFinite _)
  rw [Set.ncard_prod, Set.ncard_univ, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, hK]
    at hcard
  rw [sq]
  exact hcard

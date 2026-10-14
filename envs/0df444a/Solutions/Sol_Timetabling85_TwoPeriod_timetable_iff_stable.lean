-- Prove2me | solution 1 for Timetabling85.TwoPeriod.timetable_iff_stable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:02:49.652627+00:00
-- url     : https://prove2.me/submissions/3e2268b1-af72-4a15-add1-e4cf6dc35c8c

import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_CT4



namespace Timetabling85.TwoPeriod

open Classical

lemma eq_of_sum_le_one' {ι : Type*} [Fintype ι] (f : ι → Bool)
    (h : ∑ a, (f a).toNat ≤ 1) {a b : ι} (ha : f a = true) (hb : f b = true) : a = b := by
  by_contra hne
  have h2 : ∑ c ∈ ({a, b} : Finset ι), (f c).toNat ≤ ∑ c, (f c).toNat :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hne, ha, hb] at h2
  simp at h2
  omega

lemma sum_le_one_of_unique' {ι : Type*} [Fintype ι] (f : ι → Bool)
    (h : ∀ a b, f a = true → f b = true → a = b) : ∑ a, (f a).toNat ≤ 1 := by
  by_cases hex : ∃ a, f a = true
  · obtain ⟨a, ha⟩ := hex
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      have : f b = false := by
        by_contra hc
        exact hb (h b a (by simpa using hc) ha)
      simp [this]
    · simp
  · push Not at hex
    simp [fun a => Bool.eq_false_iff.mpr (hex a)]

lemma sum_toNat_zero' {ι : Type*} [Fintype ι] (f : ι → Bool) (h : ∑ a, (f a).toNat = 0) (a : ι) :
    f a = false := by
  have := (Finset.sum_eq_zero_iff.mp h) a (Finset.mem_univ _)
  simpa using this

theorem timetable_core {m n p : ℕ} (I : CT4Data m n p) :
    (∃ x : Fin m → Fin n → Fin p → Bool, IsSolution I x) ↔
      ∃ S : Finset (Node I), (conflictGraph I).IsNIndepSet n S := by
  have adj_iff : ∀ u v : Node I, (conflictGraph I).Adj u v ↔
      u ≠ v ∧ ((u.1 = v.1 ∨ ∃ i k, u.2.1 i k = true ∧ v.2.1 i k = true) ∨
        (v.1 = u.1 ∨ ∃ i k, v.2.1 i k = true ∧ u.2.1 i k = true)) := by
    intro u v
    unfold conflictGraph
    rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨x, hx1, hx2, hx3⟩
    have hsched : ∀ j, (fun i k => x i j k) ∈ schedules I j := by
      intro j
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · intro i; exact hx1 i j
      · intro k; exact hx3 j k
      · intro i k hik
        by_contra hb
        have hb' : I.bbar i k = false := by simpa using hb
        have h := hx2 i k
        rw [hb'] at h
        have := sum_toNat_zero' (fun j => x i j k) (by simpa using h) j
        have hik' : x i j k = true := hik
        rw [this] at hik'
        exact absurd hik' (by simp)
    let node : Fin n → Node I := fun j => ⟨j, ⟨fun i k => x i j k, hsched j⟩⟩
    have hnode : Function.Injective node := fun a b h => congrArg Sigma.fst h
    refine ⟨Finset.univ.image node, ?_, ?_⟩
    · intro u hu v hv hne hadj
      rw [Finset.mem_coe, Finset.mem_image] at hu hv
      obtain ⟨a, -, rfl⟩ := hu
      obtain ⟨b, -, rfl⟩ := hv
      have hab : a ≠ b := fun h => hne (by rw [h])
      rw [adj_iff] at hadj
      obtain ⟨-, h⟩ := hadj
      have key : ∀ (c d : Fin n), c ≠ d → ¬ (∃ i k, x i c k = true ∧ x i d k = true) := by
        rintro c d hcd ⟨i, k, h1, h2⟩
        have := eq_of_sum_le_one' (fun j => x i j k)
          (le_trans (hx2 i k) (by cases I.bbar i k <;> simp)) h1 h2
        exact hcd this
      rcases h with (h | h) | (h | h)
      · exact hab h
      · exact key a b hab h
      · exact hab h.symm
      · exact key b a hab.symm h
    · rw [Finset.card_image_of_injective _ hnode]; simp
  · rintro ⟨S, hS⟩
    have hfst : ∀ j, ∃ u ∈ S, u.1 = j := by
      have hinj : Set.InjOn Sigma.fst (S : Set (Node I)) := by
        intro u hu v hv huv
        by_contra hne
        apply hS.isIndepSet hu hv hne
        rw [adj_iff]
        exact ⟨hne, Or.inl (Or.inl huv)⟩
      have hcard : (S.image Sigma.fst).card = n := by
        rw [Finset.card_image_of_injOn hinj]; exact hS.card_eq
      have : S.image Sigma.fst = Finset.univ := by
        apply Finset.eq_univ_of_card
        simpa using hcard
      intro j
      have hj : j ∈ S.image Sigma.fst := by rw [this]; exact Finset.mem_univ _
      obtain ⟨u, hu, hu'⟩ := Finset.mem_image.mp hj
      exact ⟨u, hu, hu'⟩
    choose u hu hu1 using hfst
    have key : ∀ (v : Node I) (j : Fin n), v.1 = j → IsTeacherSchedule I j v.2.1 := by
      rintro ⟨a, y, hy⟩ j rfl
      exact (Finset.mem_filter.mp hy).2
    have hsch : ∀ j, IsTeacherSchedule I j (u j).2.1 := fun j => key (u j) j (hu1 j)
    refine ⟨fun i j k => (u j).2.1 i k, ?_, ?_, ?_⟩
    · intro i j
      have := (hsch j).1 i
      simpa using this
    · intro i k
      by_cases hb : I.bbar i k = true
      · rw [hb]
        apply sum_le_one_of_unique'
        intro a b ha hb'
        by_contra hab
        have hne : u a ≠ u b := by
          intro h
          apply hab
          rw [← hu1 a, ← hu1 b, h]
        apply hS.isIndepSet (hu a) (hu b) hne
        rw [adj_iff]
        exact ⟨hne, Or.inl (Or.inr ⟨i, k, ha, hb'⟩)⟩
      · have hb' : I.bbar i k = false := by simpa using hb
        rw [hb']
        have : ∀ j, (u j).2.1 i k = false := by
          intro j
          by_contra hc
          have := (hsch j).2.2 i k (by simpa using hc)
          rw [hb'] at this
          exact absurd this (by simp)
        simp [this]
    · intro j k
      exact (hsch j).2.1 k

end Timetabling85.TwoPeriod

open Timetabling85.TwoPeriod


theorem solution {m n p : ℕ} (I : CT4Data m n p) :
    (∃ x : Fin m → Fin n → Fin p → Bool, IsSolution I x) ↔
      ∃ S : Finset (Node I), (conflictGraph I).IsNIndepSet n S := by
  exact timetable_core I

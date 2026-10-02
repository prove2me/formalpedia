-- Prove2me | solution 1 for OptimalPAC.SampleComplexity.subsamples_subset
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:32:26.691309+00:00
-- url     : https://prove2.me/submissions/5571b460-0486-466a-95d7-fc4c05d8d0cc

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model
import Definitions.Def_OptimalPAC_SampleComplexity_Algorithm

set_option autoImplicit false

namespace OptimalPAC.SampleComplexity

theorem subsamples_subset_aux {X : Type*} (n : ℕ) : ∀ (S T : List (X × Bool)), S.length = n →
    (∀ Ŝ ∈ subsamples S T, (∀ z ∈ Ŝ, z ∈ S ++ T) ∧ (∀ z ∈ T, z ∈ Ŝ)) ∧
      ∀ T' : List (X × Bool), (subsamples S T).length = (subsamples S T').length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S T hS
  by_cases h : S.length ≤ 3
  · have e : ∀ T'' : List (X × Bool), subsamples S T'' = [S ++ T''] := fun T'' => by
      rw [subsamples, if_pos h]
    refine ⟨?_, ?_⟩
    · intro Ŝ hŜ
      rw [e, List.mem_singleton] at hŜ
      subst hŜ
      exact ⟨fun z hz => hz, fun z hz => List.mem_append_right _ hz⟩
    · intro T'
      rw [e, e]; rfl
  · obtain ⟨S0, hS0⟩ : ∃ S0, S0 = S.take (S.length - 3 * (S.length / 4)) := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A, A = (S.drop (S.length - 2 * (S.length / 4))).take (S.length / 4) :=
      ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, B = S.drop (S.length - S.length / 4) := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, C = (S.drop (S.length - 3 * (S.length / 4))).take (S.length / 4) :=
      ⟨_, rfl⟩
    have e : ∀ T'' : List (X × Bool), subsamples S T'' =
        subsamples S0 (A ++ B ++ T'') ++ subsamples S0 (C ++ B ++ T'') ++
          subsamples S0 (C ++ A ++ T'') := fun T'' => by
      rw [subsamples, if_neg h, hS0, hA, hB, hC]
    have hlt : S0.length < n := by
      rw [hS0, List.length_take]; omega
    have IH := fun T'' => ih S0.length hlt S0 T'' rfl
    have h0 : ∀ z ∈ S0, z ∈ S := fun z hz => by
      rw [hS0] at hz; exact List.mem_of_mem_take hz
    have hA' : ∀ z ∈ A, z ∈ S := fun z hz => by
      rw [hA] at hz; exact List.mem_of_mem_drop (List.mem_of_mem_take hz)
    have hB' : ∀ z ∈ B, z ∈ S := fun z hz => by
      rw [hB] at hz; exact List.mem_of_mem_drop hz
    have hC' : ∀ z ∈ C, z ∈ S := fun z hz => by
      rw [hC] at hz; exact List.mem_of_mem_drop (List.mem_of_mem_take hz)
    have key : ∀ U V : List (X × Bool), (∀ z ∈ U, z ∈ S) → (∀ z ∈ V, z ∈ S) →
        ∀ Ŝ ∈ subsamples S0 (U ++ V ++ T), (∀ z ∈ Ŝ, z ∈ S ++ T) ∧ (∀ z ∈ T, z ∈ Ŝ) := by
      intro U V hU hV Ŝ hŜ
      obtain ⟨h1, h2⟩ := (IH (U ++ V ++ T)).1 Ŝ hŜ
      refine ⟨fun z hz => ?_, fun z hz => h2 z (List.mem_append_right _ hz)⟩
      have := h1 z hz
      simp only [List.mem_append] at this ⊢
      rcases this with h | (h | h) | h
      · exact Or.inl (h0 z h)
      · exact Or.inl (hU z h)
      · exact Or.inl (hV z h)
      · exact Or.inr h
    refine ⟨?_, ?_⟩
    · intro Ŝ hŜ
      rw [e] at hŜ
      simp only [List.mem_append] at hŜ
      rcases hŜ with (h | h) | h
      · exact key A B hA' hB' Ŝ h
      · exact key C B hC' hB' Ŝ h
      · exact key C A hC' hA' Ŝ h
    · intro T'
      rw [e, e]
      simp only [List.length_append]
      rw [(IH (A ++ B ++ T)).2 (A ++ B ++ T'), (IH (C ++ B ++ T)).2 (C ++ B ++ T'),
        (IH (C ++ A ++ T)).2 (C ++ A ++ T')]

end OptimalPAC.SampleComplexity

open OptimalPAC.SampleComplexity in
theorem solution {X : Type*} (S T : List (X × Bool)) :
    (∀ Ŝ ∈ subsamples S T, (∀ z ∈ Ŝ, z ∈ S ++ T) ∧ (∀ z ∈ T, z ∈ Ŝ)) ∧
      ∀ T' : List (X × Bool), (subsamples S T).length = (subsamples S T').length := by
  exact subsamples_subset_aux S.length S T rfl

-- Prove2me | solution 1 for PCSPBLPAff.Symmetric.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T10:27:12.191456+00:00
-- url     : https://prove2.me/submissions/65adafe2-cc45-4128-9094-f6a345d3f9f4

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_PCSPBLPAff_Characterization_Setting
import Theorems.Thm_PCSPBLPAff_Characterization_lemma_7
import Theorems.Thm_PCSPBLPAff_Characterization_lemma_9

open PCSPBLPAff.Symmetric PCSPBLPAff.Characterization

/-- Symmetric polymorphisms of arbitrarily large arity are block-symmetric (one block) of
arbitrarily high width; conclude by Lemma 9 and Lemma 7. -/
theorem PCSPBLPAff.Symmetric.theorem_2_main {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A]
    [DecidableEq A] [Fintype B] (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (hT : IsPromiseTemplate 𝔸 𝔹)
    (hsym : ∀ N : ℕ, ∃ L : ℕ, N ≤ L ∧
      ∃ f : (Fin L → A) → B, IsPolymorphism 𝔸 𝔹 f ∧ IsSymmetric f) :
    CorrectlySolves 𝔸 𝔹 := by
  refine (lemma_7 𝔸 𝔹 hT).2 (lemma_9 𝔸 𝔹 (fun N => ?_))
  obtain ⟨L, hNL, f, hf, hs⟩ := hsym N
  refine ⟨L, f, hf, 1, fun _ => 0, Nat.one_pos, fun b => ?_, fun π _ x => hs π x⟩
  rw [Fin.fin_one_eq_zero b]
  simpa using hNL

theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (hT : IsPromiseTemplate 𝔸 𝔹)
    (hsym : ∀ N : ℕ, ∃ L : ℕ, N ≤ L ∧
      ∃ f : (Fin L → A) → B, IsPolymorphism 𝔸 𝔹 f ∧ IsSymmetric f) :
    CorrectlySolves 𝔸 𝔹 :=
  PCSPBLPAff.Symmetric.theorem_2_main 𝔸 𝔹 hT hsym

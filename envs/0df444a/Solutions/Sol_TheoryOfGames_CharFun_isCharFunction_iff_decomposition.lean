-- Prove2me | solution 1 for TheoryOfGames.CharFun.isCharFunction_iff_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:57:06.279376+00:00
-- url     : https://prove2.me/submissions/e7f52c63-c685-4bed-84c8-8ea3ccc4a643

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction

open TheoryOfGames.CharFun in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) :
    IsCharFunction v ↔
      ((∀ S₁ : Finset (Fin n), S₁ = Finset.univ → v S₁ = 0) ∧
        (∀ S₁ S₂ : Finset (Fin n), Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
          v S₁ + v S₂ = 0) ∧
        (∀ S₁ S₂ S₃ : Finset (Fin n), Disjoint S₁ S₂ → Disjoint S₁ S₃ → Disjoint S₂ S₃ →
          S₁ ∪ S₂ ∪ S₃ = Finset.univ → v S₁ + v S₂ + v S₃ ≤ 0)) := by
  have hcompl : ∀ S₁ S₂ : Finset (Fin n), Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
      S₂ = S₁ᶜ := by
    intro S₁ S₂ hd hu
    ext x
    simp only [Finset.mem_compl]
    constructor
    · intro hx h1
      exact Finset.disjoint_left.mp hd h1 hx
    · intro hx
      have : x ∈ S₁ ∪ S₂ := by rw [hu]; exact Finset.mem_univ x
      rcases Finset.mem_union.mp this with h | h
      · exact absurd h hx
      · exact h
  constructor
  · rintro ⟨h0, hc, hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro S₁ hS
      subst hS
      have := hc ∅
      rw [Finset.compl_empty, h0] at this
      simpa using this
    · intro S₁ S₂ hd hu
      rw [hcompl S₁ S₂ hd hu, hc S₁]
      ring
    · intro S₁ S₂ S₃ h12 h13 h23 hu
      have hd : Disjoint (S₁ ∪ S₂) S₃ := Finset.disjoint_union_left.mpr ⟨h13, h23⟩
      have h3 : S₃ = (S₁ ∪ S₂)ᶜ := hcompl _ _ hd hu
      have := hs S₁ S₂ h12
      rw [h3, hc (S₁ ∪ S₂)]
      linarith
  · rintro ⟨h1, h2, h3⟩
    have hc : ∀ S : Finset (Fin n), v Sᶜ = -v S := by
      intro S
      have := h2 S Sᶜ disjoint_compl_right (Finset.union_compl S)
      linarith
    have hu : v Finset.univ = 0 := h1 _ rfl
    refine ⟨?_, hc, ?_⟩
    · have := hc Finset.univ
      rw [Finset.compl_univ, hu] at this
      simpa using this
    · intro S T hST
      have hd1 : Disjoint S (S ∪ T)ᶜ :=
        Finset.disjoint_left.mpr (fun x hx hx' =>
          (Finset.mem_compl.mp hx') (Finset.mem_union_left _ hx))
      have hd2 : Disjoint T (S ∪ T)ᶜ :=
        Finset.disjoint_left.mpr (fun x hx hx' =>
          (Finset.mem_compl.mp hx') (Finset.mem_union_right _ hx))
      have := h3 S T (S ∪ T)ᶜ hST hd1 hd2 (Finset.union_compl (S ∪ T))
      rw [hc (S ∪ T)] at this
      linarith

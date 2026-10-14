-- Prove2me | solution 1 for StrategyProofArrow.WeakGS.lemma_9_i
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:32:09.099383+00:00
-- url     : https://prove2.me/submissions/2e096f9c-cea5-466f-be16-c67b1c2f56fe

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic



namespace StrategyProofArrow.WeakGS

theorem g4_strong_rel_iff {A : Type*} (S : StrategyProofArrow.Correspondence.StrongOrder A) {x y : A}
    (hxy : x ≠ y) : S.1.rel x y ↔ S.1.strict x y := by
  constructor
  · intro h
    exact ⟨h, fun h' => hxy (S.2 x y h h')⟩
  · intro h; exact h.1

theorem g4_reg_strict_iff {ι A : Type*}
    (γ : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A)
    (hγ : IsTieBreaking γ) (Q : StrategyProofArrow.Correspondence.StrongProfile ι A)
    (hQ : ∀ (B : WeakProfile ι A) (i : ι) (x y : A),
      (B i).rel x y → (B i).rel y x → ((γ B i).1.strict x y ↔ (Q i).1.strict x y))
    (B : WeakProfile ι A) (j : ι) (x y : A) :
    (γ B j).1.strict x y ↔
      ((B j).strict x y ∨ ((B j).rel x y ∧ (B j).rel y x ∧ (Q j).1.strict x y)) := by
  by_cases h1 : (B j).rel x y <;> by_cases h2 : (B j).rel y x
  · rw [hQ B j x y h1 h2]
    constructor
    · intro h; exact Or.inr ⟨h1, h2, h⟩
    · rintro (h | ⟨_, _, h⟩)
      · exact absurd h2 h.2
      · exact h
  · have hs : (B j).strict x y := ⟨h1, h2⟩
    simp only [hs, true_or, iff_true]
    exact hγ B j x y hs
  · have hs : (B j).strict y x := ⟨h2, h1⟩
    have := hγ B j y x hs
    constructor
    · intro h; exact absurd h.1 this.2
    · rintro (h | ⟨h, _⟩)
      · exact absurd h.1 h1
      · exact absurd h h1
  · rcases (B j).total x y with h | h
    · exact absurd h h1
    · exact absurd h h2

theorem g4_reg_local {ι A : Type*}
    (γ : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A)
    (hγ : IsRegularTieBreaking γ) (B B' : WeakProfile ι A) (j : ι) (h : B j = B' j) :
    γ B j = γ B' j := by
  obtain ⟨hγ1, Q, hQ⟩ := hγ
  apply Subtype.ext
  apply StrategyProofArrow.Correspondence.WeakOrder.ext
  funext x y
  apply propext
  by_cases hxy : x = y
  · subst hxy
    constructor
    · intro _; exact ((γ B' j).1.total x x).elim id id
    · intro _; exact ((γ B j).1.total x x).elim id id
  · rw [g4_strong_rel_iff _ hxy, g4_strong_rel_iff _ hxy,
      g4_reg_strict_iff γ hγ1 Q hQ, g4_reg_strict_iff γ hγ1 Q hQ, h]

theorem lemma_9_i_core {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (v : VotingProcedure ι A) (ν : StrictVotingProcedure ι A)
    (γ : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A)
    (hν : StrictStrategyProof ν) (hγ : IsRegularTieBreaking γ)
    (hv : ∀ B : WeakProfile ι A, v B = ν (γ B)) :
    StrategyProof v := by
  intro B i b hstr
  have hupd : γ (Function.update B i b) = Function.update (γ B) i (γ (Function.update B i b) i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]
      exact g4_reg_local γ hγ _ _ j (by rw [Function.update_of_ne hj])
  have := hν (γ B) i (γ (Function.update B i b) i)
  rw [← hupd, ← hv, ← hv] at this
  exact this (hγ.1 B i _ _ hstr)

end StrategyProofArrow.WeakGS

open StrategyProofArrow.WeakGS


theorem solution {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : VotingProcedure ι A) (ν : StrictVotingProcedure ι A)
    (γ : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A)
    (hν : StrictStrategyProof ν) (hγ : IsRegularTieBreaking γ)
    (hv : ∀ B : WeakProfile ι A, v B = ν (γ B)) :
    StrategyProof v := by
  exact lemma_9_i_core v ν γ hν hγ hv

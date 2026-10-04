-- Prove2me | solution 1 for TheoryOfGames.SimpleGames.undominated_iff_mem_uPlus
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:08:05.942985+00:00
-- url     : https://prove2.me/submissions/aa324727-816b-4437-b7a8-8b4c18972538

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority

set_option autoImplicit false

open TheoryOfGames.SimpleGames in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hs : IsSimple v) (hred : ∀ i : Fin n, v {i} = -1)
    (U : Set (Finset (Fin n))) (hU : U ⊆ minimalSets (winningSets v))
    (x : Fin n → ℝ) (hx7 : ∀ i, 0 ≤ x i) (hx8 : ∀ S ∈ U, ∑ i ∈ S, x i = (n : ℝ))
    (β : Fin n → ℝ) (hβ : IsImputation v β) :
    (∀ α ∈ mainSet U x, ¬ Dominates v α β) ↔ rSet x β ∈ uPlus U := by
  classical
  -- β i ≥ -1
  have hβ1 : ∀ i, -1 ≤ β i := fun i => by
    have := hβ.1 i; rw [hred i] at this; exact this
  -- sums of α^S over subsets of S
  have hsumα : ∀ S T : Finset (Fin n), T ⊆ S →
      ∑ i ∈ T, alphaS x S i = ∑ i ∈ T, x i - (T.card : ℝ) := by
    intro S T hTS
    have : ∀ i ∈ T, alphaS x S i = x i + (-1) := by
      intro i hi; simp [alphaS, hTS hi]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    simp; ring
  -- flat sets: v T = - card
  have hflat : ∀ T : Finset (Fin n), IsFlat v T → v T = -(T.card : ℝ) := by
    intro T hT
    unfold IsFlat at hT
    rw [hT, Finset.sum_congr rfl (fun k _ => hred k)]
    simp
  -- winning sets: v S = n - card S
  have hwin : ∀ S : Finset (Fin n), S ∈ winningSets v → v S = (n : ℝ) - (S.card : ℝ) := by
    intro S hS
    have h1 : v Sᶜ = -v S := hv.2.1 S
    have h2 := hflat Sᶜ hS
    have h3 : S.card + Sᶜ.card = n := by
      rw [Finset.card_add_card_compl, Fintype.card_fin]
    have h4 : ((S.card : ℕ) : ℝ) + ((Sᶜ.card : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast h3
    linarith
  -- n ≠ 0
  have hn : n ≠ 0 := by
    intro h0
    subst h0
    apply hs.1
    intro S
    have hS : S = ∅ := Subsingleton.elim _ _
    subst hS
    simp [reducedForm, hv.1]
  constructor
  · intro H
    simp only [uPlus, uStar, Set.mem_setOf_eq]
    rintro ⟨T, hTU, hTsub⟩
    apply H (alphaS x T) ⟨T, hTU, rfl⟩
    have hTw : T ∈ winningSets v := (hU hTU).1
    refine ⟨T, ?_, ?_, ?_⟩
    · rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      have := hx8 ∅ hTU
      simp at this
      exact hn (by exact_mod_cast this.symm)
    · unfold IsEffective
      rw [hsumα T T le_rfl, hx8 T hTU, hwin T hTw]
    · intro i hi
      have hi' := hTsub hi
      simp [rSet] at hi'
      simp [alphaS, hi]
      linarith
  · intro H
    rintro α ⟨S, hSU, rfl⟩ ⟨T, hTne, hTeff, hTlt⟩
    simp only [uPlus, uStar, Set.mem_setOf_eq] at H
    apply H
    -- T ⊆ S
    have hTS : T ⊆ S := by
      intro i hi
      by_contra hiS
      have := hTlt i hi
      simp [alphaS, hiS] at this
      linarith [hβ1 i]
    -- x i > 0 on T
    have hxpos : ∀ i ∈ T, 0 < x i := by
      intro i hi
      have := hTlt i hi
      simp [alphaS, hTS hi] at this
      linarith [hβ1 i]
    have hTw : T ∈ winningSets v := by
      rcases hs.2 T with h | h
      · exact h
      · exfalso
        have hvT := hflat T h
        unfold IsEffective at hTeff
        rw [hsumα S T hTS, hvT] at hTeff
        have : 0 < ∑ i ∈ T, x i := Finset.sum_pos hxpos hTne
        linarith
    have hTeq : T = S := by
      by_contra hne
      exact (hU hSU).2 T (lt_of_le_of_ne hTS hne) hTw
    subst hTeq
    refine ⟨T, hSU, ?_⟩
    intro i hi
    have := hTlt i hi
    simp [alphaS, hi] at this
    simp [rSet]
    linarith

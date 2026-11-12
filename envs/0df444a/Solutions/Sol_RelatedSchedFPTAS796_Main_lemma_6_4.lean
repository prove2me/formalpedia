-- Prove2me | solution 1 for RelatedSchedFPTAS796.Main.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T15:20:09.297475+00:00
-- url     : https://prove2.me/submissions/530ceef2-ff14-47c4-ad4f-8a4143a4c07a

import Mathlib

set_option autoImplicit false

open Pointwise

/-- In a finite abelian group, a subset larger than half the group satisfies `A + A = G`. -/
theorem solution {G : Type*} [AddCommGroup G] [Finite G] (A : Set G)
    (hA : (Nat.card G : ℚ) / 2 < Nat.card A) : A + A = Set.univ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  rw [Set.eq_univ_iff_forall]
  intro g
  let s : Finset G := A.toFinset
  have hs_card : s.card = Nat.card A := by
    dsimp only [s]
    rw [Nat.card_coe_set_eq, ← Set.ncard_eq_toFinset_card']
  have h2q : (Nat.card G : ℚ) < 2 * (Nat.card A : ℚ) := by linarith
  have h2 : Nat.card G < 2 * Nat.card A := by exact_mod_cast h2q
  let t : Finset G := s.image (fun a => g - a)
  have ht_card : t.card = s.card := by
    dsimp only [t]
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact sub_right_injective hab
  have hunion_le : (s ∪ t).card ≤ Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  by_contra hg
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro a ha hat
    apply hg
    rw [Set.mem_add]
    obtain ⟨a', ha', hsub⟩ := Finset.mem_image.mp hat
    refine ⟨a, ?_, a', ?_, ?_⟩
    · dsimp only [s] at ha
      exact Set.mem_toFinset.mp ha
    · dsimp only [s] at ha'
      exact Set.mem_toFinset.mp ha'
    · rw [← hsub, sub_add_cancel]
  have hcard_union : (s ∪ t).card = s.card + t.card :=
    Finset.card_union_of_disjoint hdisj
  have hlt_union : Nat.card G < (s ∪ t).card := by
    calc Nat.card G < 2 * Nat.card A := h2
      _ = 2 * s.card := by rw [hs_card]
      _ = s.card + t.card := by rw [ht_card]; omega
      _ = (s ∪ t).card := hcard_union.symm
  omega

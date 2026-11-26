-- Prove2me | solution 1 for Stanley.reciprocity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:20.202803+00:00
-- url     : https://prove2.me/submissions/ab8f93a8-9345-41af-9264-9a801b38267c

module
public import Definitions.Def_Stanley_Compatible
public import Mathlib.Tactic.Ring
public import Definitions.Def_Stanley_Reciprocity
public import Theorems.Thm_Stanley_compatibleCount_empty
public import Theorems.Thm_Stanley_compatibleCount_zero
public import Theorems.Thm_Stanley_chromaticPolynomial_empty
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
public import Theorems.Thm_Stanley_compatibleCount_succ
public import Theorems.Thm_Stanley_convolution
public import Theorems.Thm_Stanley_eval_neg_one
public import Theorems.Thm_Stanley_eval_zero
public import Theorems.Thm_Stanley_orientationCount_induce_univ
attribute [local simp] Stanley.chromaticPolynomial_induce_univ
attribute [local simp] Stanley.orientationCount_induce_univ



set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution (k : ℕ) :
    (chromaticPolynomial G).eval (-(k : ℤ)) =
      (-1 : ℤ) ^ Fintype.card V * compatibleCount G k := by
  classical
  have aux : ∀ k : ℕ, ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      (chromaticPolynomial H).eval (-(k : ℤ)) =
        (-1 : ℤ) ^ Fintype.card W * compatibleCount H k := by
    intro k
    induction k with
    | zero =>
      intro W _ H
      cases isEmpty_or_nonempty W with
      | inl h => simp [chromaticPolynomial_empty, compatibleCount_empty]
      | inr h => simp [eval_zero, compatibleCount_zero]
    | succ k ih =>
      intro W _ H
      have harg : -((k + 1 : ℕ) : ℤ) = -1 + -(k : ℤ) := by push_cast; ring
      rw [harg, convolution, compatibleCount_succ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [eval_neg_one, ih]
      have hc : Fintype.card (s : Set W) + Fintype.card ↥((s : Set W)ᶜ) =
          Fintype.card W := by
        calc
          _ = Fintype.card {v : W // v ∈ (s : Set W)} +
              Fintype.card {v : W // v ∉ (s : Set W)} := by
            congr 1
          _ = Fintype.card W := by
            rw [Fintype.card_subtype_compl]
            exact Nat.add_sub_cancel' (Fintype.card_subtype_le _)
      calc
        _ = ((-1 : ℤ) ^ Fintype.card (s : Set W) *
            (-1 : ℤ) ^ Fintype.card ↥((s : Set W)ᶜ)) *
            (orientationCount (H.induce (s : Set W)) *
              compatibleCount (H.induce (s : Set W)ᶜ) k) := by ring
        _ = _ := by rw [← pow_add, hc]
  exact aux k V G
end Stanley

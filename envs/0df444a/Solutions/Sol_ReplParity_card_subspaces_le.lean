-- Prove2me | solution 1 for ReplParity.card_subspaces_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:02:28.779777+00:00
-- url     : https://prove2.me/submissions/846fc18f-9ae2-455e-a874-627226e71c33

import Mathlib
import Definitions.Def_ReplParity_Vec

open ReplParity in
theorem solution (n : ℕ) :
    Nat.card (ReplParity.Subsp n) ≤ 2 ^ (n ^ 2) ∧
    ∃ f : ReplParity.Subsp n → (Fin n → Fin n → ZMod 2), Function.Injective f := by
  have key : ∀ W : ReplParity.Subsp n, ∃ M : Fin n → ReplParity.Vec n,
      Submodule.span (ZMod 2) (Set.range M) = W := by
    intro W
    have hk : Module.finrank (ZMod 2) W ≤ n := by
      have := Submodule.finrank_le W
      simpa using this
    let b := Module.finBasis (ZMod 2) W
    refine ⟨fun r => if h : r.val < Module.finrank (ZMod 2) W then (b ⟨r.val, h⟩ : ReplParity.Vec n)
      else 0, ?_⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      by_cases h : r.val < Module.finrank (ZMod 2) W
      · simp only [dif_pos h]
        exact (b _).2
      · simp only [dif_neg h]
        exact W.zero_mem
    · intro x hx
      have hsum := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
      rw [← hsum]
      refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨i.val, by omega⟩, ?_⟩))
      simp [i.isLt]
  choose g hg using key
  have hinj : Function.Injective g := fun W1 W2 h => by rw [← hg W1, ← hg W2, h]
  refine ⟨?_, g, hinj⟩
  have h1 := Nat.card_le_card_of_injective g hinj
  have hc : Nat.card (Fin n → ReplParity.Vec n) = 2 ^ (n ^ 2) := by
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [← pow_mul, sq]
  omega

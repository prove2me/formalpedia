-- Prove2me | solution 1 for WilliamsonShmoys.union_graph_iso
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T10:55:44.614736+00:00
-- url     : https://prove2.me/submissions/c3a99b9c-7860-4b9d-b7a6-e9098c67bcca

import Mathlib

set_option autoImplicit false

open Classical in
theorem solution {n k : ℕ} (hn : 0 < n) (edge : Fin n → Fin n → Bool) (lvl : Fin n → ℕ)
    (mk : ℕ → ℕ) (eb : ℕ → ℕ → ℕ) (hmk : ∀ v : Fin n, mk v.val = lvl v % k)
    (heb : ∀ v w : Fin n, (1 ≤ eb v.val w.val ↔ edge v w = true)) :
    ∀ a b : Fin k × Fin n,
      (SimpleGraph.fromRel (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ mk (x.val % n) ≠ x.val / n ∧
          mk (y.val % n) ≠ x.val / n ∧ 1 ≤ eb (x.val % n) (y.val % n)) = true)).Adj
        (finProdFinEquiv a) (finProdFinEquiv b) ↔
      (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧
        (SimpleGraph.fromRel (fun u v => edge u v = true)).Adj x.2 y.2 ∧
        lvl x.2 % k ≠ x.1.val ∧ lvl y.2 % k ≠ x.1.val)).Adj a b := by
  intro a b
  have hd : ∀ x : Fin k × Fin n, (finProdFinEquiv x).val / n = x.1.val ∧ (finProdFinEquiv x).val % n = x.2.val := by
    intro x
    simp only [finProdFinEquiv_apply_val]
    constructor
    · rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt x.2.isLt, Nat.zero_add]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt]
  obtain ⟨a1, a2⟩ := hd a
  obtain ⟨b1, b2⟩ := hd b
  have hinj : finProdFinEquiv a ≠ finProdFinEquiv b ↔ a ≠ b := finProdFinEquiv.injective.ne_iff
  simp only [SimpleGraph.fromRel_adj, decide_eq_true_eq, a1, a2, b1, b2, hinj, hmk, heb, ne_eq]
  constructor
  · rintro ⟨hne, h | h⟩
    · have hc : a.1 = b.1 := Fin.ext h.1
      have h2 : a.2 ≠ b.2 := fun e => hne (Prod.ext hc e)
      exact ⟨hne, Or.inl ⟨hc, ⟨h2, Or.inl h.2.2.2⟩, h.2.1, h.2.2.1⟩⟩
    · have hc : b.1 = a.1 := Fin.ext h.1
      have h2 : b.2 ≠ a.2 := fun e => hne (Prod.ext hc.symm e.symm)
      exact ⟨hne, Or.inr ⟨hc, ⟨h2, Or.inl h.2.2.2⟩, h.2.1, h.2.2.1⟩⟩
  · rintro ⟨hne, ⟨hc, ⟨-, he | he⟩, m1, m2⟩ | ⟨hc, ⟨-, he | he⟩, m1, m2⟩⟩
    · exact ⟨hne, Or.inl ⟨congrArg Fin.val hc, m1, m2, he⟩⟩
    · exact ⟨hne, Or.inr ⟨congrArg Fin.val hc.symm, by rw [← hc]; exact m2, by rw [← hc]; exact m1, he⟩⟩
    · exact ⟨hne, Or.inr ⟨congrArg Fin.val hc, m1, m2, he⟩⟩
    · exact ⟨hne, Or.inl ⟨congrArg Fin.val hc.symm, by rw [← hc]; exact m2, by rw [← hc]; exact m1, he⟩⟩

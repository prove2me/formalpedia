-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_budget
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:42:33.157977+00:00
-- url     : https://prove2.me/submissions/e4aba728-7e21-4483-97bd-ba2a9eba8a3e

import Definitions.Def_ResourceScheduling_Graph_RAMBudget

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

private theorem join_bound (B a b A C d e : ℕ)
    (ha : a ≤ A * (B + 1)^d) (hb : b ≤ C * (B + 1)^e) :
    a + b + 1 ≤ (A + C + 1) * (B + 1)^(max d e) := by
  have hd := Nat.mul_le_mul_left A (pow_le_pow_right' (by omega : 1 ≤ B + 1) (le_max_left d e))
  have he := Nat.mul_le_mul_left C (pow_le_pow_right' (by omega : 1 ≤ B + 1) (le_max_right d e))
  have hp := one_le_pow₀ (n := max d e) (by omega : 1 ≤ B + 1)
  nlinarith

theorem solution {V : Type} [DecidableEq V] (p : RAMCode V) (B : ℕ) (s : RAMState V)
    (h : p.Bounded B s) : p.cost s ≤ p.weight * (B + 1)^p.degree := by
  induction p generalizing s with
  | seq p q ihp ihq =>
    have hh := join_bound B _ _ _ _ _ _ (ihp s h.1) (ihq (p.eval s) h.2)
    simpa [RAMCode.cost, RAMCode.weight, RAMCode.degree, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hh
  | branch v p q ihp ihq =>
    have hh := join_bound B _ _ _ _ _ _ (ihp s h.1) (ihq s h.2)
    have hm : max (p.cost s) (q.cost s) ≤ p.cost s + q.cost s := max_le (by omega) (by omega)
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; omega
  | loop v p ih =>
    let f := fun s : RAMState V => p.eval (s.set v (s.val v - 1))
    have hc : ∀ i ∈ Finset.range (s.val v),
        1 + 1 + p.cost (((f^[i]) s).set v (((f^[i]) s).val v - 1)) + 2 ≤
          p.weight * (B + 1)^p.degree + 4 := by
      intro i hi
      have hh := ih _ (h.2 i (Finset.mem_range.mp hi))
      dsimp [f] at ⊢; omega
    have hh := Finset.sum_le_sum hc
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hh
    have hn : s.val v ≤ B := h.1.1 v
    have hp := one_le_pow₀ (n := p.degree) (by omega : 1 ≤ B + 1)
    change (∑ i ∈ Finset.range (s.val v),
      (1 + 1 + p.cost (((f^[i]) s).set v (((f^[i]) s).val v - 1)) + 2)) + 1 ≤ _
    dsimp only [RAMCode.weight, RAMCode.degree]
    rw [pow_succ]
    have hm := Nat.mul_le_mul_right (p.weight * (B + 1)^p.degree + 4) hn
    nlinarith
  | mul i j dst hneq =>
    have hi := h.1 i; have hj := h.1 j; have hd := h.1 dst
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]
    have hm := Nat.mul_le_mul hi hj
    nlinarith
  | sub i j dst =>
    have hi := h.1 i; have hj := h.1 j; have hd := h.1 dst
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | bit i dst =>
    have hi := h.1 i; have hd := h.1 dst; have hw := h.2
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | copy i dst hneq =>
    have hi := h.1 i; have hd := h.1 dst
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | parse t good hneq =>
    have ht := h.1 t; have hg := h.1 good; have hw := h.2
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | length dst =>
    have hd := h.1 dst; have hw := h.2
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | zero v | emit v | add v _ _ =>
    have hv := h.1 v
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | _ =>
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]
    exact Nat.succ_le_of_lt (by positivity)

#print axioms solution

-- Prove2me | solution 1 for TensorNP.SymEigen.stabTensor_symmetric_cubicForm
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:59:39.732534+00:00
-- url     : https://prove2.me/submissions/a700471a-7106-4c7b-964b-c00ab511fc95

import Mathlib
import Definitions.Def_TensorNP_SymEigen_Defs
import Definitions.Def_TensorNP_SymEigen_StabTensor

namespace Aux_TensorNP_SymEigen_stabTensor_symmetric_cubicForm

open TensorNP.SymEigen

lemma m1 {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Multiset α) = {a, c, b} := by
  rw [Multiset.insert_eq_cons a, Multiset.insert_eq_cons a, Multiset.pair_comm]

lemma m2 {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Multiset α) = {b, a, c} := by
  simp only [Multiset.insert_eq_cons]
  exact Multiset.cons_swap _ _ _

lemma pair {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (v1 v2 : α) (h : v1 ≠ v2)
    (b : α) :
    (∑ c, if ({b, c} : Multiset α) = {v1, v2} then f b * f c else 0) =
      if b = v1 then f v1 * f v2 else if b = v2 then f v2 * f v1 else 0 := by
  by_cases h1 : b = v1
  · subst h1
    rw [if_pos rfl]
    have : ∀ c, (({b, c} : Multiset α) = {b, v2}) ↔ c = v2 := by
      intro c
      simp only [Multiset.insert_eq_cons, Multiset.cons_inj_right, Multiset.singleton_inj]
    rw [Finset.sum_eq_single v2]
    · rw [if_pos rfl]
    · intro c _ hc
      rw [if_neg (fun h' => hc ((this c).1 h'))]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg h1]
    by_cases h2 : b = v2
    · subst h2
      rw [if_pos rfl]
      have : ∀ c, (({b, c} : Multiset α) = {v1, b}) ↔ c = v1 := by
        intro c
        rw [Multiset.pair_comm v1 b]
        simp only [Multiset.insert_eq_cons, Multiset.cons_inj_right, Multiset.singleton_inj]
      rw [Finset.sum_eq_single v1]
      · rw [if_pos ((this v1).2 rfl)]
      · intro c _ hc
        rw [if_neg (fun h' => hc ((this c).1 h'))]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    · rw [if_neg h2]
      apply Finset.sum_eq_zero
      intro c _
      rw [if_neg]
      intro h'
      have : b ∈ ({v1, v2} : Multiset α) := h' ▸ (by simp)
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at this
      rcases this with h3 | h3
      · exact h1 h3
      · exact h2 h3

lemma pairsum {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (v1 v2 : α) (h : v1 ≠ v2) :
    (∑ b, ∑ c, if ({b, c} : Multiset α) = {v1, v2} then f b * f c else 0) =
      2 * f v1 * f v2 := by
  simp only [pair f v1 v2 h]
  have : ∀ b, (if b = v1 then f v1 * f v2 else if b = v2 then f v2 * f v1 else 0) =
      (if b = v1 then f v1 * f v2 else 0) + (if b = v2 then f v2 * f v1 else 0) := by
    intro b
    by_cases h1 : b = v1
    · subst h1; simp [h]
    · simp [h1]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma triple {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (u1 u2 u3 : α)
    (h12 : u1 ≠ u2) (h13 : u1 ≠ u3) (h23 : u2 ≠ u3) :
    (∑ a, ∑ b, ∑ c, if ({a, b, c} : Multiset α) = {u1, u2, u3} then f a * f b * f c else 0) =
      6 * f u1 * f u2 * f u3 := by
  have key : ∀ a, (∑ b, ∑ c,
      if ({a, b, c} : Multiset α) = {u1, u2, u3} then f a * f b * f c else 0) =
      (if a = u1 then f u1 * (2 * f u2 * f u3) else 0) +
      (if a = u2 then f u2 * (2 * f u1 * f u3) else 0) +
      (if a = u3 then f u3 * (2 * f u1 * f u2) else 0) := by
    intro a
    have reduce : ∀ (w1 w2 : α), w1 ≠ w2 → ({u1, u2, u3} : Multiset α) = {a, w1, w2} →
        (∑ b, ∑ c, if ({a, b, c} : Multiset α) = {u1, u2, u3} then f a * f b * f c else 0)
          = f a * (2 * f w1 * f w2) := by
      intro w1 w2 hw hM
      rw [← pairsum f w1 w2 hw, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro c _
      rw [hM]
      have : (({a, b, c} : Multiset α) = {a, w1, w2}) ↔ (({b, c} : Multiset α) = {w1, w2}) := by
        simp only [Multiset.insert_eq_cons, Multiset.cons_inj_right]
      by_cases hc : ({b, c} : Multiset α) = {w1, w2}
      · rw [if_pos (this.2 hc), if_pos hc]; ring
      · rw [if_neg (fun h' => hc (this.1 h')), if_neg hc, mul_zero]
    by_cases ha1 : a = u1
    · subst ha1
      rw [reduce u2 u3 h23 rfl, if_pos rfl, if_neg h12, if_neg h13]; ring
    by_cases ha2 : a = u2
    · subst ha2
      rw [reduce u1 u3 h13 (m2 _ _ _), if_neg (Ne.symm h12), if_pos rfl, if_neg h23]; ring
    by_cases ha3 : a = u3
    · subst ha3
      rw [reduce u1 u2 h12 (by rw [m1, m2]), if_neg (Ne.symm h13), if_neg (Ne.symm h23),
        if_pos rfl]; ring
    rw [if_neg ha1, if_neg ha2, if_neg ha3]
    simp only [add_zero]
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _
    rw [if_neg]
    intro h'
    have : a ∈ ({u1, u2, u3} : Multiset α) := h' ▸ (by simp)
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at this
    tauto
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end Aux_TensorNP_SymEigen_stabTensor_symmetric_cubicForm

open Aux_TensorNP_SymEigen_stabTensor_symmetric_cubicForm in
open TensorNP.SymEigen in
theorem solution {v : ℕ} (G : SimpleGraph (Fin v)) :
    IsSymmetric (stabTensor G) ∧
      ∀ z : Idx v → ℝ, cubicForm (stabTensor G) z =
        6 * nesterovForm G (fun i => z (Sum.inl i)) (fun p => z (Sum.inr p)) := by
  classical
  have hst : ∀ a b c a' b' c' : Idx v, ({a, b, c} : Multiset (Idx v)) = {a', b', c'} →
      stabTensor G a b c = stabTensor G a' b' c' := by
    intro a b c a' b' c' h
    unfold stabTensor
    rw [h]
  refine ⟨fun i j k => ⟨hst _ _ _ _ _ _ (m1 _ _ _), hst _ _ _ _ _ _ (m2 _ _ _),
    hst _ _ _ _ _ _ (by rw [m2, m1]), hst _ _ _ _ _ _ (by rw [m1, m2]),
    hst _ _ _ _ _ _ (by rw [m1, m2, m1])⟩, fun z => ?_⟩
  set M : PairIdx v → Multiset (Idx v) :=
    fun p => {Sum.inl p.1.1, Sum.inl p.1.2, Sum.inr p} with hM
  set NE := Finset.univ.filter (fun p : PairIdx v => ¬ G.Adj p.1.1 p.1.2) with hNE
  have huniq : ∀ p q : PairIdx v, M p = M q → p = q := by
    intro p q h
    have : (Sum.inr p : Idx v) ∈ M q := h ▸ (by simp [hM])
    simp [hM] at this
    exact this
  have hrepr : ∀ a b c, stabTensor G a b c =
      ∑ p ∈ NE, if ({a, b, c} : Multiset (Idx v)) = M p then 1 else 0 := by
    intro a b c
    unfold stabTensor
    by_cases hex : ∃ p : PairIdx v, ¬ G.Adj p.1.1 p.1.2 ∧
        ({a, b, c} : Multiset (Idx v)) = {Sum.inl p.1.1, Sum.inl p.1.2, Sum.inr p}
    · rw [if_pos hex]
      obtain ⟨p0, hp0, hm0⟩ := hex
      rw [Finset.sum_eq_single p0]
      · rw [if_pos hm0]
      · intro q _ hq
        rw [if_neg]
        intro h'
        exact hq (huniq _ _ (h'.symm.trans hm0))
      · intro h'; exact absurd (by simp [hNE, hp0]) h'
    · rw [if_neg hex]
      symm
      apply Finset.sum_eq_zero
      intro p hp
      rw [if_neg]
      intro h'
      simp only [hNE, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hex ⟨p, hp, h'⟩
  unfold cubicForm nesterovForm
  simp only [hrepr, Finset.sum_mul]
  have hswap : ∀ (g : Idx v → Idx v → Idx v → PairIdx v → ℝ),
      (∑ a, ∑ b, ∑ c, ∑ p ∈ NE, g a b c p) = ∑ p ∈ NE, ∑ a, ∑ b, ∑ c, g a b c p := by
    intro g
    calc (∑ a, ∑ b, ∑ c, ∑ p ∈ NE, g a b c p) = ∑ a, ∑ b, ∑ p ∈ NE, ∑ c, g a b c p :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))
      _ = ∑ a, ∑ p ∈ NE, ∑ b, ∑ c, g a b c p :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ p ∈ NE, ∑ a, ∑ b, ∑ c, g a b c p := Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hp := p.2
  have h12 : (Sum.inl p.1.1 : Idx v) ≠ Sum.inl p.1.2 :=
    fun h => (ne_of_lt hp) (Sum.inl_injective h)
  have h13 : (Sum.inl p.1.1 : Idx v) ≠ Sum.inr p := Sum.inl_ne_inr
  have h23 : (Sum.inl p.1.2 : Idx v) ≠ Sum.inr p := Sum.inl_ne_inr
  rw [← mul_assoc, ← mul_assoc, ← triple z _ _ _ h12 h13 h23]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  by_cases hc : ({a, b, c} : Multiset (Idx v)) = M p
  · rw [if_pos hc, if_pos hc]; ring
  · rw [if_neg hc, if_neg hc]; ring

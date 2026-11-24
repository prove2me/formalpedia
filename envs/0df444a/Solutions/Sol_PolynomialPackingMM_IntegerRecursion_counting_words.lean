-- Prove2me | solution 1 for PolynomialPackingMM.IntegerRecursion.counting_words
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:22:14.560015+00:00
-- url     : https://prove2.me/submissions/ecbe9f84-325e-4dad-a043-b04595e9483f

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

open scoped BigOperators
open PolynomialPackingMM.IntegerRecursion

namespace CountingWordsAux
open Finset

/-- Number of positions of a word carrying a left-tagged letter. -/
def lc {d : ℕ} {α β : Type} (u : Fin d → α ⊕ β) : ℕ :=
  ((List.finRange d).filter (fun i => (u i).isLeft)).length

lemma lc_le {d : ℕ} {α β : Type} (u : Fin d → α ⊕ β) : lc u ≤ d := by
  unfold lc
  calc _ ≤ (List.finRange d).length := List.length_filter_le _ _
    _ = d := List.length_finRange

lemma lc_swap {d : ℕ} {α β : Type} (u : Fin d → α ⊕ β) :
    lc (fun i => (u i).swap) + lc u = d := by
  unfold lc
  have h := List.length_eq_length_filter_add (l := List.finRange d) (fun i => (u i).isLeft)
  simp only [List.length_finRange] at h
  have e : (fun i => (Sum.swap (u i)).isLeft) = (fun i => !(u i).isLeft) := by
    funext i; cases u i <;> rfl
  rw [e]; omega

/-- Number of words in `Fin n → Fin f ⊕ Fin g` with exactly `i` left letters. -/
def cnt (n f g i : ℕ) : ℕ := #(univ.filter (fun u : Fin n → Fin f ⊕ Fin g => lc u = i))

lemma total (n f g : ℕ) : (f + g) ^ n = ∑ i ∈ range (n + 1), cnt n f g i := by
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n → Fin f ⊕ Fin g)))
    (t := range (n + 1)) (f := lc)
    (by intro u _; simp only [coe_range, Set.mem_Iio]; exact Nat.lt_succ_of_le (lc_le u))
  rw [card_univ, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin] at h
  exact h

lemma cnt_swap (n f g j : ℕ) (hj : j ≤ n) :
    #(univ.filter (fun v : Fin n → Fin g ⊕ Fin f => lc v = n - j)) = cnt n f g j := by
  unfold cnt
  apply card_nbij' (fun v k => (v k).swap) (fun u k => (u k).swap)
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hv ⊢
    have := lc_swap v; omega
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hu ⊢
    have := lc_swap u; omega
  · intro v _; funext k; simp
  · intro u _; funext k; simp

lemma bal (n f g : ℕ) :
    balancedWordCount f g n = ∑ i ∈ range (n + 1), cnt n f g i ^ 2 := by
  unfold balancedWordCount
  rw [card_filter, Fintype.sum_prod_type]
  have step : ∀ u : Fin n → Fin f ⊕ Fin g,
      (∑ v : Fin n → Fin g ⊕ Fin f, if fullLetters (u, v) = n then 1 else 0) = cnt n f g (lc u) := by
    intro u
    rw [← cnt_swap n f g (lc u) (lc_le u), card_filter]
    apply sum_congr rfl
    intro v _
    have hu := lc_le u
    have e : fullLetters (u, v) = lc u + lc v := rfl
    rw [e]
    split_ifs <;> omega
  rw [sum_congr rfl (fun u _ => step u)]
  rw [← sum_fiberwise_of_maps_to' (s := univ) (t := range (n + 1)) (g := lc)
    (fun u _ => by simp only [mem_range]; exact Nat.lt_succ_of_le (lc_le u))]
  apply sum_congr rfl
  intro i _
  rw [sum_const, smul_eq_mul, sq]
  rfl

lemma main (f g n : ℕ) :
    ((f + g : ℕ) : ℚ) ^ (2 * n) / ((n : ℚ) + 1) ≤ (balancedWordCount f g n : ℚ) := by
  have cs := sq_sum_le_card_mul_sum_sq (s := range (n + 1)) (f := fun i => (cnt n f g i : ℚ))
  rw [card_range] at cs
  rw [div_le_iff₀ (by positivity), pow_mul', ← Nat.cast_pow, total, bal]
  push_cast at cs ⊢
  linarith [cs]

end CountingWordsAux

theorem solution :
  ∀ (f g : ℕ) (d : ℕ+), 1 ≤ f + g →
  ((f + g : ℕ) : ℚ) ^ (2 * (d : ℕ)) / ((d : ℕ) + 1 : ℚ) ≤
    (balancedWordCount f g d : ℚ) := by
  intro f g d _
  exact CountingWordsAux.main f g d

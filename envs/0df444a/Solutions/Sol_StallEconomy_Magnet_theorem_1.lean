-- Prove2me | solution 1 for StallEconomy.Magnet.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:14:50.939593+00:00
-- url     : https://prove2.me/submissions/6e4599b7-c036-4024-a056-9eabeca6cebb

import Mathlib
import Definitions.Def_StallEconomy_Magnet_Setting
import Theorems.Thm_StallEconomy_Magnet_row_count
import Theorems.Thm_StallEconomy_Magnet_column_count_type1
import Theorems.Thm_StallEconomy_Magnet_column_count_type2
import Theorems.Thm_StallEconomy_Magnet_positive_transition

namespace StallEconomy.Magnet

/-- Main assembly from the counting facts (row sums, column sums, positivity). -/
lemma theorem_1_of (k h : ℕ) (hkh : 2 * h ≤ k)
    (hrow : ∀ zo : ℤ × ℤ, zo ∈ inner k h → ∑ zd : inner k h, (A k h zo zd.1).card = (k + 1) ^ 2)
    (hcol : ∀ zd : ℤ × ℤ, zd ∈ inner k h → ∑ zo : inner k h, (A k h zo.1 zd).card = (k + 1) ^ 2)
    (hpos : ∀ zo zd : inner k h, 0 < (A k h zo.1 zd.1).card) :
    P k h ∈ doublyStochastic ℝ (inner k h) ∧
      ∀ π : inner k h → ℝ,
        MarkovChain.IsStationary (P k h) π ↔
          π = MarkovChain.unif (inner k h) := by
  have hK : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have hrowR : ∀ i : inner k h, ∑ j, P k h i j = 1 := by
    intro i
    simp only [P]
    rw [← Finset.sum_div, ← Nat.cast_sum, hrow i.1 i.2]
    push_cast
    exact div_self hK.ne'
  have hcolR : ∀ j : inner k h, ∑ i, P k h i j = 1 := by
    intro j
    simp only [P]
    rw [← Finset.sum_div, ← Nat.cast_sum, hcol j.1 j.2]
    push_cast
    exact div_self hK.ne'
  have hposR : ∀ i j : inner k h, 0 < P k h i j := by
    intro i j
    simp only [P]
    exact div_pos (by exact_mod_cast hpos i j) hK
  have hne : Nonempty (inner k h) := by
    refine ⟨⟨((h : ℤ), (h : ℤ)), ?_⟩⟩
    simp only [inner, Finset.mem_product, Finset.mem_Icc]
    omega
  have hcard : (0 : ℝ) < (Fintype.card (inner k h) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨?_, ?_⟩
  · rw [mem_doublyStochastic_iff_sum]
    exact ⟨fun i j => (hposR i j).le, hrowR, hcolR⟩
  intro π
  constructor
  · rintro ⟨⟨hnn, hsum⟩, hfix⟩
    obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ π Finset.univ_nonempty
    have e : ∑ i, π i * P k h i j0 = π j0 := by
      have := congrFun hfix j0
      simpa [Matrix.vecMul, dotProduct] using this
    have hz : ∑ i, (π j0 - π i) * P k h i j0 = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hcolR, e, mul_one, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (sub_nonneg.2 (hj0 i (Finset.mem_univ _))) (hposR i j0).le)).1 hz
    have hall : ∀ i, π i = π j0 := by
      intro i
      have := hterm i (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h1 | h1
      · linarith
      · exact absurd h1 (hposR i j0).ne'
    have hs : (Fintype.card (inner k h) : ℝ) * π j0 = 1 := by
      rw [← hsum]
      simp [hall]
    funext i
    rw [hall i]
    simp only [MarkovChain.unif]
    field_simp
    linarith
  · rintro rfl
    refine ⟨⟨fun _ => ?_, ?_⟩, ?_⟩
    · simp only [MarkovChain.unif]; positivity
    · simp only [MarkovChain.unif, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    · funext j
      simp only [Matrix.vecMul, dotProduct, MarkovChain.unif]
      rw [← Finset.mul_sum, hcolR, mul_one]

end StallEconomy.Magnet

open StallEconomy.Magnet

theorem solution (k h : ℕ) (hkh : 2 * h ≤ k) :
    P k h ∈ doublyStochastic ℝ (inner k h) ∧
      ∀ π : inner k h → ℝ,
        MarkovChain.IsStationary (P k h) π ↔
          π = MarkovChain.unif (inner k h) := by
  refine theorem_1_of k h hkh (fun zo hzo => row_count k h hkh zo hzo) ?_
    (fun zo zd => positive_transition k h hkh zo zd)
  intro zd hzd
  by_cases ht : zd ∈ type1 k h
  · exact column_count_type1 k h hkh zd ht
  · exact column_count_type2 k h hkh zd hzd ht

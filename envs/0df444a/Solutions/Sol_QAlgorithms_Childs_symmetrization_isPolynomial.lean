-- Prove2me | solution 1 for QAlgorithms.Childs.symmetrization_isPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:33:27.254287+00:00
-- url     : https://prove2.me/submissions/f55c088c-4a29-4165-a901-29b49d13d185

import Definitions.Def_QAlgorithms_Defs_Polynomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open QAlgorithms
open scoped BigOperators

private def bitSet {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

private def setBits {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

private lemma bitSet_setBits {n : ℕ} (s : Finset (Fin n)) : bitSet (setBits s) = s := by
  ext i
  simp [bitSet, setBits]

private lemma setBits_bitSet {n : ℕ} (x : Fin n → Bool) : setBits (bitSet x) = x := by
  funext i
  simp [bitSet, setBits]

private lemma monomial_bool {n : ℕ} (d : Fin n →₀ ℕ) (a : ℝ) (x : Fin n → Bool) :
    MvPolynomial.eval (boolPoint x) (MvPolynomial.monomial d a) =
      a * if d.support ⊆ bitSet x then 1 else 0 := by
  classical
  rw [MvPolynomial.eval_monomial]
  congr 1
  change (∏ i ∈ d.support, boolPoint x i ^ d i) = _
  split_ifs with h
  · apply Finset.prod_eq_one
    intro i hi
    have hx : x i = true := (Finset.mem_filter.mp (h hi)).2
    simp [boolPoint, hx]
  · obtain ⟨i, hi, hn⟩ := Finset.not_subset.mp h
    have hx : x i = false := by simpa [bitSet] using hn
    exact Finset.prod_eq_zero hi (by simp [boolPoint, hx, Finsupp.mem_support_iff.mp hi])

private lemma sum_bits_count {n : ℕ} (s : Finset (Fin n)) (k : ℕ) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => hammingWeight x = k),
      if s ⊆ bitSet x then (1 : ℝ) else 0) =
      (((Finset.univ.powersetCard k).filter (s ⊆ ·)).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  apply Finset.card_bij (fun x _ => bitSet x)
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx, hs⟩
    have hk := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hk⟩, hs⟩
  · intro x hx y hy hxy
    simpa only [setBits_bitSet] using congrArg setBits hxy
  · intro s' hs'
    rcases Finset.mem_filter.mp hs' with ⟨hs', hss'⟩
    have hk := (Finset.mem_powersetCard.mp hs').2
    refine ⟨setBits s', ?_, bitSet_setBits s'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by change (bitSet (setBits s')).card = k; rw [bitSet_setBits]; exact hk,
      by simpa only [bitSet_setBits] using hss'⟩

private lemma monomial_average {n : ℕ} (d : Fin n →₀ ℕ) (a : ℝ) (k : ℕ) (hk : k ≤ n) :
    weightAverage (MvPolynomial.monomial d a) k =
      a * ((k.descFactorial d.support.card : ℝ) / (n.descFactorial d.support.card : ℝ)) := by
  classical
  have hs : d.support.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ d.support)
  have hn : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk)
  have hd : (n.choose d.support.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hs)
  have hf : (d.support.card.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [weightAverage, monomial_bool, ← Finset.mul_sum]
  rw [sum_bits_count]
  by_cases hsk : d.support.card ≤ k
  · rw [Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _) hsk]
    simp only [Finset.card_univ, Fintype.card_fin]
    have hc := Nat.choose_mul (n := n) hsk
    have hc' : (n.choose k : ℝ) * (k.choose d.support.card : ℝ) =
        (n.choose d.support.card : ℝ) * ((n - d.support.card).choose (k - d.support.card) : ℝ) := by
      exact_mod_cast hc
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
    nlinarith [congrArg (fun z : ℝ => a * z) hc']
  · have he : ((Finset.univ.powersetCard k).filter (d.support ⊆ ·) : Finset (Finset (Fin n))) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨ht, hst⟩
      exact hsk ((Finset.card_le_card hst).trans_eq (Finset.mem_powersetCard.mp ht).2)
    rw [he, Finset.card_empty, Nat.cast_zero, mul_zero, Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hsk)]
    simp

private lemma weightAverage_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℝ) (k : ℕ) :
    weightAverage (∑ i ∈ s, f i) k = ∑ i ∈ s, weightAverage (f i) k := by
  classical
  simp only [weightAverage, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma support_card_le_degree {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (d : Fin n →₀ ℕ) (hd : d ∈ p.support) :
    d.support.card ≤ p.totalDegree := by
  have he : d.sum (fun _ e => e) = d.support.card := by
    change (∑ i ∈ d.support, d i) = _
    calc
      _ = ∑ i ∈ d.support, 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hpos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
        have hle := (MvPolynomial.le_degreeOf_of_mem_support i hd).trans (hp i)
        omega
      _ = _ := by simp
  rw [← he]
  exact MvPolynomial.le_totalDegree hd

theorem solution (n : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ p.totalDegree ∧
      ∀ k : ℕ, k ≤ n → Q.eval (k : ℝ) = weightAverage p k := by
  classical
  let f : (Fin n →₀ ℕ) → Polynomial ℝ := fun d =>
    Polynomial.C (p.coeff d / (n.descFactorial d.support.card : ℝ)) *
      descPochhammer ℝ d.support.card
  refine ⟨∑ d ∈ p.support, f d, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro d hd
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((descPochhammer_natDegree ℝ _).le.trans (support_card_le_degree p hp d hd))
  · intro k hk
    calc
      _ = ∑ d ∈ p.support,
          p.coeff d * ((k.descFactorial d.support.card : ℝ) / (n.descFactorial d.support.card : ℝ)) := by
        simp only [Polynomial.eval_finsetSum, f, Polynomial.eval_mul, Polynomial.eval_C,
          descPochhammer_eval_eq_descFactorial]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = ∑ d ∈ p.support, weightAverage (MvPolynomial.monomial d (p.coeff d)) k := by
        apply Finset.sum_congr rfl
        intro d hd
        exact (monomial_average d (p.coeff d) k hk).symm
      _ = weightAverage (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d)) k :=
        (weightAverage_sum _ _ _).symm
      _ = weightAverage p k := congrArg (fun q => weightAverage q k) (MvPolynomial.as_sum p).symm

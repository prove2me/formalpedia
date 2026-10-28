-- Prove2me | solution 1 for WernerExt.TwoSided.min_casimir
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T18:36:01.575771+00:00
-- url     : https://prove2.me/submissions/797969af-ce20-47b6-b7b1-b85af490d5ff

import Definitions.Def_WernerExt_TwoSided_Model
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19

namespace WernerExt.TwoSided

open Finset

/-- Abel's inequality: nonnegative partial sums against a nonnegative antitone weight. -/
theorem abel_nonneg : ∀ (n : ℕ) (δ a : ℕ → ℝ), (∀ k ≤ n, 0 ≤ ∑ i ∈ range k, δ i) →
    (∀ i j, i ≤ j → j < n → a j ≤ a i) → (∀ i < n, 0 ≤ a i) →
    0 ≤ ∑ i ∈ range n, δ i * a i := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro δ a hD ha ha0
    have hsplit : ∑ i ∈ range (n + 1), δ i * a i =
        ∑ i ∈ range n, δ i * (a i - a n) + a n * ∑ i ∈ range (n + 1), δ i := by
      rw [sum_range_succ, sum_range_succ, mul_add, Finset.mul_sum]
      simp only [mul_sub, sum_sub_distrib]
      have : ∑ i ∈ range n, δ i * a n = ∑ i ∈ range n, a n * δ i := by
        congr 1; ext i; ring
      rw [this]; ring
    rw [hsplit]
    have h1 : 0 ≤ ∑ i ∈ range n, δ i * (a i - a n) :=
      ih δ (fun i => a i - a n) (fun k hk => hD k (by omega))
        (fun i j hij hj => by linarith [ha i j hij (by omega)])
        (fun i hi => by linarith [ha i n hi.le (by omega)])
    have h2 : 0 ≤ a n * ∑ i ∈ range (n + 1), δ i := mul_nonneg (ha0 n (by omega)) (hD _ le_rfl)
    linarith

/-- `∑_{i<n} δ_i (n-1-i) = ∑_{k<n} ∑_{i<k} δ_i`. -/
theorem weight_identity : ∀ (n : ℕ) (δ : ℕ → ℝ),
    ∑ i ∈ range n, δ i * ((n : ℝ) - 1 - i) = ∑ k ∈ range n, ∑ i ∈ range k, δ i := by
  intro n δ
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ (fun k => ∑ i ∈ range k, δ i), ← ih]
    push_cast
    have : ∑ i ∈ range n, δ i * ((n : ℝ) + 1 - 1 - i) =
        ∑ i ∈ range n, δ i * ((n : ℝ) - 1 - i) + ∑ i ∈ range n, δ i := by
      rw [← sum_add_distrib]; congr 1; ext i; ring
    rw [this]; ring

/-- ℕ-indexed extension of a row vector. -/
noncomputable def extN {d : ℕ} (l : Fin d → ℕ) (i : ℕ) : ℝ :=
  if h : i < d then (l ⟨i, h⟩ : ℝ) else 0

theorem sum_fin_eq {d : ℕ} (f : ℕ → ℝ) : ∑ i : Fin d, f i = ∑ i ∈ range d, f i :=
  Fin.sum_univ_eq_sum_range f d

theorem extN_fin {d : ℕ} (l : Fin d → ℕ) (i : Fin d) : extN l i = l i := by
  simp [extN, i.2]

theorem partial_eq {d : ℕ} (l : Fin d → ℕ) (k : ℕ) (hk : k ≤ d) :
    ((∑ i ∈ univ.filter (fun i : Fin d => i.val < k), l i : ℕ) : ℝ) = ∑ i ∈ range k, extN l i := by
  push_cast
  rw [sum_filter]
  have : ∑ i : Fin d, (if (i : ℕ) < k then (l i : ℝ) else 0) =
      ∑ i : Fin d, (fun j : ℕ => if j < k then extN l j else 0) i := by
    congr 1; ext i; simp only [extN_fin]
  rw [this, sum_fin_eq (fun j : ℕ => if j < k then extN l j else 0), ← sum_filter]
  congr 1
  ext j; simp only [mem_filter, mem_range]; omega

/-- The Casimir difference of two rows with equal sums. -/
theorem casimir_diff {d : ℕ} (l m : Fin d → ℕ) (h : ∑ i, l i = ∑ i, m i) :
    casimirValue l - casimirValue m =
      ∑ i : Fin d, (((l i : ℝ) ^ 2 - (m i : ℝ) ^ 2) +
        2 * ((d : ℝ) - 1 - (i : ℕ)) * ((l i : ℝ) - m i)) := by
  have hR : ∑ k, (l k : ℝ) = ∑ k, (m k : ℝ) := by exact_mod_cast h
  unfold casimirValue
  rw [hR, ← sum_sub_distrib]
  set s := (∑ k, (m k : ℝ)) / d
  have : ∀ i : Fin d, (((l i : ℝ) - s) ^ 2 + 2 * ((d : ℝ) - 1 - (i : ℕ)) * ((l i : ℝ) - s)) -
      (((m i : ℝ) - s) ^ 2 + 2 * ((d : ℝ) - 1 - (i : ℕ)) * ((m i : ℝ) - s)) =
      (((l i : ℝ) ^ 2 - (m i : ℝ) ^ 2) + 2 * ((d : ℝ) - 1 - (i : ℕ)) * ((l i : ℝ) - m i)) +
        (-2 * s) * ((l i : ℝ) - m i) := by intro i; ring
  simp only [this, sum_add_distrib, ← mul_sum, sum_sub_distrib, hR, sub_self, mul_zero, add_zero]

theorem casimir_dominance_aux (d n : ℕ) (hd : 2 ≤ d) :
    (∀ l m : DPart d n, Covers l m → casimirValue m.1 + 1 ≤ casimirValue l.1) ∧
      (∀ l m : DPart d n, Dominates l.1 m.1 → l ≠ m → casimirValue m.1 < casimirValue l.1) ∧
      (∀ (l m : DPart d n) (i k : Fin d), i < k → l.1 i = m.1 i + 1 → l.1 k + 1 = m.1 k →
        (∀ r : Fin d, r ≠ i → r ≠ k → l.1 r = m.1 r) →
        casimirValue l.1 - casimirValue m.1 =
          2 * (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ) + ((m.1 i : ℝ) - (m.1 k : ℝ)) + 1)) := by
  -- strict monotonicity
  have hstrict : ∀ l m : DPart d n, Dominates l.1 m.1 → l ≠ m →
      0 < casimirValue l.1 - casimirValue m.1 := by
    intro l m hdom hne
    have hsum : ∑ i, l.1 i = ∑ i, m.1 i := by rw [l.2.2, m.2.2]
    rw [casimir_diff l.1 m.1 hsum]
    set L := extN l.1
    set M := extN m.1
    set δ : ℕ → ℝ := fun i => L i - M i
    have hconv : ∀ i : Fin d, (((l.1 i : ℝ) ^ 2 - (m.1 i : ℝ) ^ 2) +
        2 * ((d : ℝ) - 1 - (i : ℕ)) * ((l.1 i : ℝ) - m.1 i)) =
        (fun j : ℕ => δ j * (L j + M j) + 2 * (δ j * ((d : ℝ) - 1 - j))) i := by
      intro i; simp only [δ, L, M, extN_fin]; ring
    simp only [hconv]
    rw [sum_fin_eq (fun j : ℕ => δ j * (L j + M j) + 2 * (δ j * ((d : ℝ) - 1 - j))),
      sum_add_distrib, ← mul_sum, weight_identity]
    -- partial sums
    have hD : ∀ k ≤ d, 0 ≤ ∑ i ∈ range k, δ i := by
      intro k hk
      have hk' := hdom k
      have e1 := partial_eq l.1 k hk
      have e2 := partial_eq m.1 k hk
      have : ((∑ i ∈ univ.filter (fun i : Fin d => i.val < k), m.1 i : ℕ) : ℝ) ≤
          ((∑ i ∈ univ.filter (fun i : Fin d => i.val < k), l.1 i : ℕ) : ℝ) := by
        exact_mod_cast hk'
      simp only [δ, sum_sub_distrib]; linarith
    have hDd : ∑ i ∈ range d, δ i = 0 := by
      have e1 := partial_eq l.1 d le_rfl
      have e2 := partial_eq m.1 d le_rfl
      have hf : univ.filter (fun i : Fin d => i.val < d) = univ := by
        ext i; simp [i.2]
      rw [hf] at e1 e2
      simp only [δ, sum_sub_distrib]
      rw [← e1, ← e2, hsum]; ring
    have hab := abel_nonneg d δ (fun j => L j + M j) hD
      (fun i j hij hj => by
        simp only [L, M, extN, dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
        have h1 := l.2.1 (show (⟨i, by omega⟩ : Fin d) ≤ ⟨j, hj⟩ from hij)
        have h2 := m.2.1 (show (⟨i, by omega⟩ : Fin d) ≤ ⟨j, hj⟩ from hij)
        have h1' : (l.1 ⟨j, hj⟩ : ℝ) ≤ l.1 ⟨i, by omega⟩ := by exact_mod_cast h1
        have h2' : (m.1 ⟨j, hj⟩ : ℝ) ≤ m.1 ⟨i, by omega⟩ := by exact_mod_cast h2
        linarith)
      (fun i hi => by simp only [L, M, extN, dif_pos hi]; positivity)
    -- some partial sum is positive
    have hpos : ∃ k ∈ range d, 0 < ∑ i ∈ range k, δ i := by
      by_contra hcon
      push Not at hcon
      have hzero : ∀ k ≤ d, ∑ i ∈ range k, δ i = 0 := by
        intro k hk
        rcases Nat.lt_or_ge k d with h | h
        · exact le_antisymm (hcon k (mem_range.mpr h)) (hD k hk)
        · rw [show k = d by omega]; exact hDd
      apply hne
      apply Subtype.ext
      funext i
      have h1 := hzero (i.val + 1) (by omega)
      have h0 := hzero i.val (by omega)
      rw [sum_range_succ, h0, zero_add] at h1
      simp only [δ, L, M, extN, dif_pos i.2] at h1
      have : (l.1 i : ℝ) = m.1 i := by linarith
      exact_mod_cast this
    obtain ⟨k, hk, hkpos⟩ := hpos
    have hsumpos : 0 < ∑ k ∈ range d, ∑ i ∈ range k, δ i :=
      lt_of_lt_of_le hkpos (single_le_sum (fun j hj => hD j (by
        simp at hj; omega)) hk)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro l m hcov
    obtain ⟨hdom, hne, -⟩ := hcov
    have hp := hstrict l m hdom hne
    have hsum : ∑ i, l.1 i = ∑ i, m.1 i := by rw [l.2.2, m.2.2]
    have hdiff := casimir_diff l.1 m.1 hsum
    set z : ℤ := ∑ i : Fin d, (((l.1 i : ℤ) ^ 2 - (m.1 i : ℤ) ^ 2) +
        2 * ((d : ℤ) - 1 - (i : ℕ)) * ((l.1 i : ℤ) - m.1 i)) with hz
    have hzR : (z : ℝ) = ∑ i : Fin d, (((l.1 i : ℝ) ^ 2 - (m.1 i : ℝ) ^ 2) +
        2 * ((d : ℝ) - 1 - (i : ℕ)) * ((l.1 i : ℝ) - m.1 i)) := by
      rw [hz]; push_cast; rfl
    rw [← hzR] at hdiff
    have hp' : (0 : ℝ) < z := by linarith
    have hz1 : (1 : ℤ) ≤ z := by exact_mod_cast hp'
    have : (1 : ℝ) ≤ z := by exact_mod_cast hz1
    linarith
  · intro l m hdom hne
    linarith [hstrict l m hdom hne]
  · intro l m i k hik hi hk hr
    have hsum : ∑ i, l.1 i = ∑ i, m.1 i := by rw [l.2.2, m.2.2]
    rw [casimir_diff l.1 m.1 hsum]
    have hne : i ≠ k := ne_of_lt hik
    rw [Fintype.sum_eq_add i k hne (fun x hx => by
      rw [hr x hx.1 hx.2]; ring)]
    have hi' : (l.1 i : ℝ) = m.1 i + 1 := by exact_mod_cast hi
    have hk' : (l.1 k : ℝ) = m.1 k - 1 := by
      have : (l.1 k : ℝ) + 1 = m.1 k := by exact_mod_cast hk
      linarith
    rw [hi', hk']
    ring

open QAlgorithms.Schur QAlgorithms.Papers.Independent.Frontier30.P19

theorem card_eq_sum_rowLen (d : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d) :
    ∑ i : Fin d, μ.rowLen i = μ.cells.card := by
  rw [Fin.sum_univ_eq_sum_range (fun i => μ.rowLen i) d]
  have hmaps : ∀ c ∈ μ.cells, c.1 ∈ range d := by
    intro c hc
    have h0 : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) hc
    rw [YoungDiagram.mem_iff_lt_colLen] at h0
    exact mem_range.mpr (lt_of_lt_of_le h0 hμ)
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_congr rfl
  intro i _
  rw [YoungDiagram.rowLen_eq_card]
  congr 1

/-- The `d`-partition of a Young diagram with at most `d` rows. -/
def toDPart {d n : ℕ} (l : Partition d n) : DPart d n :=
  ⟨fun i => l.val.rowLen i, fun i j hij => l.val.rowLen_anti _ _ hij,
    by rw [card_eq_sum_rowLen d l.val l.2.2]; exact l.2.1⟩

theorem min_casimir (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB)
    (lA : Partition d nA) (lB : Partition d nB) (l0 : Partition d (nA + nB))
    (h0 : 0 < lrCoefficient d lA.val lB.val l0.val)
    (hmin : ∀ lAB : Partition d (nA + nB), 0 < lrCoefficient d lA.val lB.val lAB.val →
      Dominates (fun i : Fin d => lAB.val.rowLen i) (fun i : Fin d => l0.val.rowLen i)) :
    ∀ lAB : Partition d (nA + nB), 0 < lrCoefficient d lA.val lB.val lAB.val →
      casimirValue (fun i : Fin d => l0.val.rowLen i) ≤
        casimirValue (fun i : Fin d => lAB.val.rowLen i) := by
  intro lAB hpos
  have hdom := hmin lAB hpos
  by_cases heq : (fun i : Fin d => lAB.val.rowLen i) = (fun i : Fin d => l0.val.rowLen i)
  · rw [heq]
  · have hne : toDPart lAB ≠ toDPart l0 := by
      intro h; apply heq; exact congrArg Subtype.val h
    exact ((casimir_dominance_aux d (nA + nB) hd).2.1 (toDPart lAB) (toDPart l0) hdom hne).le

end WernerExt.TwoSided


-- Platform entry point: restates the target verbatim.
namespace WernerExt.TwoSided

open QAlgorithms.Schur QAlgorithms.Papers.Independent.Frontier30.P19

/-- p. 3: if the set of irreps appearing in `λ^A ⊗ λ^B` has a minimum `λ^0` in dominance
order, then `λ^0` has the smallest quadratic Casimir eigenvalue among the product diagrams. -/
theorem _root_.solution (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB)
    (lA : Partition d nA) (lB : Partition d nB) (l0 : Partition d (nA + nB))
    (h0 : 0 < lrCoefficient d lA.val lB.val l0.val)
    (hmin : ∀ lAB : Partition d (nA + nB), 0 < lrCoefficient d lA.val lB.val lAB.val →
      Dominates (fun i : Fin d => lAB.val.rowLen i) (fun i : Fin d => l0.val.rowLen i)) :
    ∀ lAB : Partition d (nA + nB), 0 < lrCoefficient d lA.val lB.val lAB.val →
      casimirValue (fun i : Fin d => l0.val.rowLen i) ≤
        casimirValue (fun i : Fin d => lAB.val.rowLen i) := by
  apply @WernerExt.TwoSided.min_casimir <;> assumption

end WernerExt.TwoSided

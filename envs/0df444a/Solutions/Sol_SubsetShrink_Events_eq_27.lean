-- Prove2me | solution 1 for SubsetShrink.Events.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T20:25:14.759502+00:00
-- url     : https://prove2.me/submissions/50cfb1c6-ba6e-4a0f-b5a5-35f5072e377b

/-
  DS7 target: SubsetShrink.Events.eq_27
  theorem_id 8f4331a0-06ce-4d47-a5f1-4da2695c7723 (Open milestone of mission
  b3f99725-2ef4-482e-8cc0-ff264fd019ff).

  Deterministic groundwork for prob_F: l2(Xu) ≤ l1 u ≤ √s l2 u for l0 u ≤ s and
  unit-norm columns, plus the weight comparison used in the definition of F vs E.
-/
import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory
open SubsetShrink.Events
open scoped BigOperators

private lemma l1_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ l1 v :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private lemma l2_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ l2 v := Real.sqrt_nonneg _

/-- Cauchy–Schwarz on two unit columns of `X`. -/
private lemma col_dot_abs_le_one {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (j k : Fin p) : |∑ i, X i j * X i k| ≤ 1 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => X i j) (fun i => X i k)
  rw [hX j, hX k, mul_one] at hcs
  exact (sq_le_one_iff_abs_le_one _).mp hcs

/-- `l2 (X u) ≤ l1 u` for a matrix with unit-norm columns. -/
private lemma l2_mulVec_le_l1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (u : Fin p → ℝ) : l2 (X.mulVec u) ≤ l1 u := by
  have hS2 : (l2 (X.mulVec u)) ^ 2 ≤ (l1 u) ^ 2 := by
    rw [l2, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    have hexp : ∑ i, (X.mulVec u i) ^ 2
        = ∑ j : Fin p, ∑ k : Fin p, u j * u k * (∑ i : Fin n, X i j * X i k) := by
      simp only [Matrix.mulVec_apply_eq_sum, sq]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro i _
      ring
    have hrhs : (l1 u) ^ 2 = ∑ j : Fin p, ∑ k : Fin p, |u j| * |u k| := by
      rw [l1, sq, Finset.sum_mul_sum]
    rw [hexp, hrhs]
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro k _
    calc u j * u k * (∑ i : Fin n, X i j * X i k)
        ≤ |u j * u k * (∑ i : Fin n, X i j * X i k)| := le_abs_self _
      _ = |u j * u k| * |∑ i : Fin n, X i j * X i k| := abs_mul _ _
      _ ≤ |u j * u k| * 1 := by
          gcongr; exact col_dot_abs_le_one X hX j k
      _ = |u j| * |u k| := by rw [abs_mul, mul_one]
  calc l2 (X.mulVec u) = Real.sqrt ((l2 (X.mulVec u)) ^ 2) := (Real.sqrt_sq (l2_nonneg _)).symm
    _ ≤ Real.sqrt ((l1 u) ^ 2) := Real.sqrt_le_sqrt hS2
    _ = l1 u := Real.sqrt_sq (l1_nonneg u)

/-- `l1 u ≤ √(l0 u) · l2 u` by Cauchy–Schwarz on the support. -/
private lemma l1_le_sqrt_card_l2 {p : ℕ} (u : Fin p → ℝ) :
    l1 u ≤ Real.sqrt (l0 u) * l2 u := by
  set S : Finset (Fin p) := Finset.univ.filter (fun j => u j ≠ 0) with hSdef
  have hcard : S.card = l0 u := rfl
  have memS : ∀ j, j ∈ S ↔ u j ≠ 0 := by
    intro j
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
  have hzero : ∀ x, x ∉ S → u x = 0 := by
    intro x hx
    by_contra h
    exact hx ((memS x).mpr h)
  have hl1 : ∑ j ∈ S, |u j| = l1 u := by
    rw [l1]
    refine Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => ?_)
    rw [hzero x hx, abs_zero]
  have hsumsq : ∑ j ∈ S, |u j| ^ 2 = (l2 u) ^ 2 := by
    have h1 : ∑ j ∈ S, |u j| ^ 2 = ∑ j ∈ S, (u j) ^ 2 := by
      apply Finset.sum_congr rfl; intro j _; rw [sq_abs]
    have h2 : ∑ j ∈ S, (u j) ^ 2 = ∑ j, (u j) ^ 2 := by
      refine Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => ?_)
      rw [hzero x hx]; ring
    rw [h1, h2, l2, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun j => |u j|)
  rw [hl1, hsumsq, hcard] at hcs
  have hl0nn : (0 : ℝ) ≤ (l0 u : ℝ) := Nat.cast_nonneg _
  calc l1 u = Real.sqrt ((l1 u) ^ 2) := (Real.sqrt_sq (l1_nonneg u)).symm
    _ ≤ Real.sqrt ((l0 u : ℝ) * (l2 u) ^ 2) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (l0 u) * l2 u := by
        rw [Real.sqrt_mul hl0nn, Real.sqrt_sq (l2_nonneg u)]

theorem solution {n p s : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (hs : 1 ≤ s) (hsp : s ≤ p) (u : Fin p → ℝ) (hu : l0 u ≤ s) :
    l2 (X.mulVec u) ≤ l1 u ∧ l1 u ≤ Real.sqrt s * l2 u ∧
      Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u) ≤
        Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hs)
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := lt_of_lt_of_le (by norm_num) (le_trans hs hsp)
    exact_mod_cast this
  have hspR : (s : ℝ) ≤ (p : ℝ) := by exact_mod_cast hsp
  have hp1 : (0 : ℕ) < p := lt_of_lt_of_le (by norm_num) (le_trans hs hsp)
  refine ⟨l2_mulVec_le_l1 X hX u, ?_, ?_⟩
  · have h2 : Real.sqrt (l0 u) * l2 u ≤ Real.sqrt (s : ℝ) * l2 u :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hu)) (l2_nonneg u)
    exact le_trans (l1_le_sqrt_card_l2 u) h2
  · -- weight comparison
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)
    have hLnn : 0 ≤ Real.log (2 * Real.exp 1 * p / s) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hsR]
      nlinarith [hspR, hpR, he]
    have hsqrt : Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p))))
        = Real.sqrt (Real.log (2 * Real.exp 1 * p / s)) := by
      congr 1
      rw [one_div_div]
    have hl2b : l2 (X.mulVec u) ≤ Real.sqrt s * l2 u := by
      have h2 : Real.sqrt (l0 u) * l2 u ≤ Real.sqrt (s : ℝ) * l2 u :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hu)) (l2_nonneg u)
      exact le_trans (l2_mulVec_le_l1 X hX u) (le_trans (l1_le_sqrt_card_l2 u) h2)
    calc Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u)
        = Real.sqrt (Real.log (2 * Real.exp 1 * p / s)) * l2 (X.mulVec u) := by rw [hsqrt]
      _ ≤ Real.sqrt (Real.log (2 * Real.exp 1 * p / s)) * (Real.sqrt s * l2 u) :=
          mul_le_mul_of_nonneg_left hl2b (Real.sqrt_nonneg _)
      _ = (Real.sqrt s * Real.sqrt (Real.log (2 * Real.exp 1 * p / s))) * l2 u := by ring
      _ = Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u := by
          rw [Real.sqrt_mul (show (0 : ℝ) ≤ (s : ℝ) by positivity)]

-- Prove2me | solution 1 for ZudilinZeta.zudilin_small_values_criterion
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T10:07:10.569752+00:00
-- url     : https://prove2.me/submissions/9651eef9-1bc8-42a1-ae99-f95c35fb7044

import Theorems.Thm_ZudilinZeta_zudilin_lemma1

open ZudilinZeta

private lemma common_denominator {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, ∃ b : ℤ, (d : ℝ) * (q i : ℝ) = (b : ℝ) := by
  classical
  let d : ℕ := ∏ i, (q i).den
  refine ⟨d, Finset.prod_pos (fun i _ => (q i).den_pos), ?_⟩
  intro i
  obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
  refine ⟨(t : ℤ) * (q i).num, ?_⟩
  change ((∏ j, (q j).den : ℕ) : ℝ) * (q i : ℝ) = _
  rw [ht, Rat.cast_def]
  push_cast
  have hden : ((q i).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q i).den_ne_zero
  field_simp

theorem solution (P : Params) (hr : P.r = 3)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ Lambda P n ≠ 0 ∧ |Lambda P n| < ε) :
    ∃ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), Irrational (zetaR (P.r + 2 * k)) := by
  classical
  by_contra! hrat
  let I := Finset.Icc 1 ((P.q - P.r - 2) / 2)
  have hrat' (i : I) : ∃ q : ℚ, zetaR (P.r + 2 * i.val) = (q : ℝ) :=
    exists_rat_of_not_irrational (hrat i.val i.property)
  choose q hq using hrat'
  obtain ⟨d, hd, hint⟩ := common_denominator q
  choose b hb using hint
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  obtain ⟨n, hn, hnzero, hnsmall⟩ := hsmall (1 / (d : ℝ)) (one_div_pos.mpr hdR)
  obtain ⟨a, ha⟩ := (zudilin_lemma1 P n hn).2
  have hform : Lambda P n = (a 0 : ℝ) +
      ∑ i : I, (a i.val : ℝ) * zetaR (P.r + 2 * i.val) := by
    exact ha.trans (congrArg (fun x : ℝ => (a 0 : ℝ) + x)
      (Finset.sum_coe_sort I (fun k : ℕ => (a k : ℝ) * zetaR (P.r + 2 * k))).symm)
  have hb' (i : I) : (d : ℝ) * zetaR (P.r + 2 * i.val) = (b i : ℝ) := by
    rw [hq i]
    exact hb i
  let v : ℤ := (d : ℤ) * a 0 + ∑ i : I, a i.val * b i
  have hv : (v : ℝ) = (d : ℝ) * Lambda P n := by
    dsimp [v]
    push_cast
    rw [hform, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← hb' i]
    ring
  have hvzero : v ≠ 0 := by
    intro hv0
    have : (d : ℝ) * Lambda P n = 0 := by rw [← hv, hv0, Int.cast_zero]
    exact (mul_ne_zero hdR.ne' hnzero) this
  have hvge : (1 : ℝ) ≤ |(v : ℝ)| := by exact_mod_cast Int.one_le_abs hvzero
  have hvlt : |(v : ℝ)| < 1 := by
    rw [hv, abs_mul, abs_of_pos hdR]
    have := mul_lt_mul_of_pos_left hnsmall hdR
    simpa [ne_of_gt hdR] using this
  linarith

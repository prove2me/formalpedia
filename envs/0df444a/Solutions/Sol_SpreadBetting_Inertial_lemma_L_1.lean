-- Prove2me | solution 1 for SpreadBetting.Inertial.lemma_L_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:28:24.374948+00:00
-- url     : https://prove2.me/submissions/9f59c156-c5dc-4a98-8109-b64abfdd2359

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution (x : ℕ → ℝ) (hx : ∀ n : ℕ, 1 ≤ n → x n ∈ Set.Ioo 0 (1 / 2)) :
    let y : ℕ → ℝ := fun n => ∏ m ∈ Finset.Icc 1 n, (1 / 2 - x m) / (1 / 2 + x m)
    ((1 / 4 : EReal) < Filter.liminf (fun n : ℕ => ((n * x n : ℝ) : EReal)) atTop →
      Summable y) ∧
    (Filter.limsup (fun n : ℕ => ((n * x n : ℝ) : EReal)) atTop < (1 / 4 : EReal) →
      ¬ Summable y) := by
  intro y
  -- basic facts
  have hy_succ : ∀ n : ℕ, y (n + 1) = y n * ((1 / 2 - x (n + 1)) / (1 / 2 + x (n + 1))) := by
    intro n
    simp only [y]
    rw [Finset.prod_Icc_succ_top (by omega)]
  have hy_pos : ∀ n : ℕ, 0 < y n := by
    intro n
    simp only [y]
    apply Finset.prod_pos
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    obtain ⟨h1, h2⟩ := hx m hm1
    apply div_pos <;> linarith
  -- the step relation, cleared of denominators
  have hstep : ∀ n : ℕ, y (n + 1) * (1 / 2 + x (n + 1)) = y n * (1 / 2 - x (n + 1)) := by
    intro n
    obtain ⟨h1, h2⟩ := hx (n + 1) (by omega)
    rw [hy_succ]
    field_simp
  refine ⟨?_, ?_⟩
  · intro hlim
    obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.1 hlim
    have ha : (1 / 4 : ℝ) < a := by
      have : ((1 / 4 : ℝ) : EReal) < (a : EReal) := by
        convert ha1 using 1
        rfl
      exact_mod_cast this
    have hev : ∀ᶠ n : ℕ in atTop, (a : EReal) < ((n * x n : ℝ) : EReal) :=
      Filter.eventually_lt_of_lt_liminf ha2
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 hev
    set q : ℝ := (4 * a + 1) / 2 with hq
    have hq1 : 1 < q := by rw [hq]; linarith
    have hqa : q < 4 * a := by rw [hq]; linarith
    obtain ⟨N2, hN2⟩ := exists_nat_ge (q * (1 - 2 * a) / (4 * a - q))
    set N := max N1 N2 with hN
    -- Raabe-type inequality
    have key : ∀ n : ℕ, N ≤ n → (q - 1) * y (n + 1) ≤ n * y n - (n + 1) * y (n + 1) := by
      intro n hn
      have hxn : a < (n + 1 : ℝ) * x (n + 1) := by
        have := hN1 (n + 1) (by omega)
        have h' : (a : ℝ) < ((n + 1 : ℕ) : ℝ) * x (n + 1) := by exact_mod_cast this
        push_cast at h'
        exact h'
      have hn2 : (q * (1 - 2 * a) / (4 * a - q)) ≤ n := by
        have : (N2 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) hn)
        linarith
      have hn3 : q * (1 - 2 * a) ≤ n * (4 * a - q) := by
        rw [div_le_iff₀ (by linarith)] at hn2
        linarith
      obtain ⟨h1, h2⟩ := hx (n + 1) (by omega)
      have hyn := hy_pos n
      have hs := hstep n
      -- (2n+q) x ≥ q/2
      have hcore : q / 2 ≤ (2 * n + q) * x (n + 1) := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have e1 : (2 * n + q) * ((n + 1) * x (n + 1)) ≥ (2 * n + q) * a := by
          apply mul_le_mul_of_nonneg_left hxn.le; linarith
        have e2 : (2 * n + q) * a ≥ q / 2 * (n + 1) := by nlinarith
        have : (n + 1 : ℝ) * ((2 * n + q) * x (n + 1)) ≥ (n + 1) * (q / 2) := by nlinarith
        exact le_of_mul_le_mul_left this (by positivity)
      -- multiply out using y(n+1)(1/2+x) = y n (1/2 - x)
      have hyn1 := hy_pos (n + 1)
      have hden : 0 < 1 / 2 + x (n + 1) := by linarith
      have goal' : ((q - 1) * y (n + 1) + (n + 1) * y (n + 1)) * (1 / 2 + x (n + 1))
          ≤ (n * y n) * (1 / 2 + x (n + 1)) := by
        have lhs : ((q - 1) * y (n + 1) + (n + 1) * y (n + 1)) * (1 / 2 + x (n + 1))
            = (q + n) * (y n * (1 / 2 - x (n + 1))) := by rw [← hs]; ring
        rw [lhs]
        nlinarith
      have := le_of_mul_le_mul_right goal' hden
      linarith
    -- telescoping bound
    have tel : ∀ M : ℕ, (q - 1) * ∑ k ∈ Finset.range M, y (N + k + 1) + (N + M : ℕ) * y (N + M)
        ≤ N * y N := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
        rw [Finset.sum_range_succ]
        have := key (N + M) (by omega)
        push_cast at this ih ⊢
        have e : (N : ℝ) + (M + 1) = (N + M) + 1 := by ring
        rw [e]
        have e2 : N + (M + 1) = N + M + 1 := by ring
        rw [e2]
        nlinarith
    have hsum : Summable (fun k => y (k + (N + 1))) := by
      apply summable_of_sum_range_le (c := N * y N / (q - 1))
      · intro k; exact (hy_pos _).le
      · intro M
        have h := tel M
        have hnn : 0 ≤ ((N + M : ℕ) : ℝ) * y (N + M) := by
          have := hy_pos (N + M); positivity
        rw [le_div_iff₀ (by linarith)]
        have e : ∑ i ∈ Finset.range M, y (i + (N + 1)) = ∑ k ∈ Finset.range M, y (N + k + 1) := by
          apply Finset.sum_congr rfl; intro i _; congr 1; omega
        rw [e]; nlinarith
    exact (summable_nat_add_iff (N + 1)).1 hsum
  · intro hlim hsum
    obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 hlim
    have hb : b < (1 / 4 : ℝ) := by
      have : (b : EReal) < ((1 / 4 : ℝ) : EReal) := by
        convert hb2 using 1
        rfl
      exact_mod_cast this
    have hev : ∀ᶠ n : ℕ in atTop, ((n * x n : ℝ) : EReal) < (b : EReal) :=
      Filter.eventually_lt_of_limsup_lt hb1
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 hev
    obtain ⟨N2, hN2⟩ := exists_nat_ge (1 / (1 - 4 * b))
    set N := max N1 N2 with hN
    have key : ∀ n : ℕ, N ≤ n → (n + 1) * y n ≤ (n + 2) * y (n + 1) := by
      intro n hn
      have hxn : (n + 1 : ℝ) * x (n + 1) < b := by
        have := hN1 (n + 1) (by omega)
        have h' : ((n + 1 : ℕ) : ℝ) * x (n + 1) < b := by exact_mod_cast this
        push_cast at h'
        exact h'
      obtain ⟨h1, h2⟩ := hx (n + 1) (by omega)
      have hb0 : 0 < b := by
        have : 0 < (n + 1 : ℝ) * x (n + 1) := by positivity
        linarith
      have hn2 : 1 / (1 - 4 * b) ≤ n := by
        have : (N2 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) hn)
        linarith
      have hn3 : 1 ≤ n * (1 - 4 * b) := by
        rw [div_le_iff₀ (by linarith)] at hn2
        linarith
      -- (2n+3) x ≤ 1/2
      have hcore : (2 * n + 3) * x (n + 1) ≤ 1 / 2 := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have e1 : (n + 1 : ℝ) * ((2 * n + 3) * x (n + 1)) ≤ (2 * n + 3) * b := by nlinarith
        have e2 : (2 * n + 3) * b ≤ (n + 1) * (1 / 2) := by nlinarith
        exact le_of_mul_le_mul_left (by linarith) (by positivity : (0:ℝ) < n + 1)
      have hs := hstep n
      have hyn := hy_pos n
      have hden : 0 < 1 / 2 + x (n + 1) := by linarith
      have goal' : ((n + 1) * y n) * (1 / 2 + x (n + 1))
          ≤ ((n + 2) * y (n + 1)) * (1 / 2 + x (n + 1)) := by
        have rhs : ((n + 2) * y (n + 1)) * (1 / 2 + x (n + 1)) = (n + 2) * (y n * (1 / 2 - x (n + 1))) := by
          rw [← hs]; ring
        rw [rhs]
        nlinarith
      exact le_of_mul_le_mul_right goal' hden
    have mono : ∀ M : ℕ, (N + 1 : ℝ) * y N ≤ (N + M + 1 : ℕ) * y (N + M) := by
      intro M
      induction M with
      | zero => push_cast; simp
      | succ M ih =>
        have := key (N + M) (by omega)
        push_cast at this ih ⊢
        have e2 : N + (M + 1) = N + M + 1 := by ring
        rw [e2]
        nlinarith
    set c := (N + 1 : ℝ) * y N with hc
    have hc0 : 0 < c := by have := hy_pos N; positivity
    have hs2 : Summable (fun M : ℕ => y (M + N)) := (summable_nat_add_iff N).2 hsum
    have hs3 : Summable (fun M : ℕ => c / ((M + N + 1 : ℕ) : ℝ)) := by
      refine Summable.of_nonneg_of_le (fun M => by positivity) (fun M => ?_) hs2
      have h := mono M
      rw [div_le_iff₀ (by positivity)]
      have e : N + M = M + N := by ring
      rw [e] at h
      linarith [mul_comm (y (M + N)) ((M + N + 1 : ℕ) : ℝ)]
    have hs4 : Summable (fun M : ℕ => 1 / ((M + (N + 1) : ℕ) : ℝ)) := by
      have := hs3.mul_left (1 / c)
      refine this.congr (fun M => ?_)
      have e' : (M + N + 1 : ℕ) = (M + (N + 1) : ℕ) := by ring
      rw [e']
      field_simp
    have hs5 : Summable (fun M : ℕ => 1 / (M : ℝ)) :=
      (summable_nat_add_iff (f := fun M : ℕ => 1 / (M : ℝ)) (N + 1)).1 (by
        refine hs4.congr (fun M => ?_); push_cast; ring_nf)
    exact Real.not_summable_one_div_natCast hs5

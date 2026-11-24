-- Prove2me | solution 1 for OrderedSearchExact.Exact.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:27:39.00545+00:00
-- url     : https://prove2.me/submissions/e48a0cfc-a939-4c9f-89eb-addae2636574

import Definitions.Def_OrderedSearchExact_Exact_Packets

open OrderedSearchExact.Exact Finset

lemma OSx_quad (x : ℕ → ℝ) (n : ℕ) (θ : ℝ) :
    ∑ k ∈ range n, ∑ l ∈ range n, x k * x l * Real.cos ((k:ℝ) * θ - (l:ℝ) * θ) =
      (∑ k ∈ range n, x k * Real.cos ((k:ℝ) * θ)) ^ 2 +
        (∑ k ∈ range n, x k * Real.sin ((k:ℝ) * θ)) ^ 2 := by
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [Real.cos_sub]; ring

lemma OSx_regroup (F : ℕ → ℕ → ℝ) (θ : ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1), F k l * Real.cos ((k:ℝ) * θ - (l:ℝ) * θ) =
      ∑ k ∈ range (n + 1), F k k + ∑ j ∈ range n, Real.cos (((j:ℝ) + 1) * θ) *
        ∑ k ∈ range (n - j), (F k (k + j + 1) + F (k + j + 1) k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hL : ∑ k ∈ range (n + 1 + 1), ∑ l ∈ range (n + 1 + 1),
          F k l * Real.cos ((k:ℝ) * θ - (l:ℝ) * θ) =
        (∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1), F k l * Real.cos ((k:ℝ) * θ - (l:ℝ) * θ)) +
        ∑ k ∈ range (n + 1), (F k (n + 1) * Real.cos ((k:ℝ) * θ - ((n + 1 : ℕ):ℝ) * θ) +
          F (n + 1) k * Real.cos (((n + 1 : ℕ):ℝ) * θ - (k:ℝ) * θ)) + F (n + 1) (n + 1) := by
      rw [Finset.sum_range_succ (fun k => ∑ l ∈ range (n + 1 + 1), _),
        Finset.sum_congr rfl (fun k _ => Finset.sum_range_succ
          (fun l => F k l * Real.cos ((k:ℝ) * θ - (l:ℝ) * θ)) (n + 1)),
        Finset.sum_range_succ (fun l => F (n + 1) l * Real.cos (((n + 1 : ℕ):ℝ) * θ - (l:ℝ) * θ)),
        Finset.sum_add_distrib, Finset.sum_add_distrib, sub_self, Real.cos_zero, mul_one]
      ring
    have hsplit : ∀ j ∈ range (n + 1), Real.cos (((j:ℝ) + 1) * θ) *
          ∑ k ∈ range (n + 1 - j), (F k (k + j + 1) + F (k + j + 1) k) =
        Real.cos (((j:ℝ) + 1) * θ) * ∑ k ∈ range (n - j), (F k (k + j + 1) + F (k + j + 1) k) +
        Real.cos (((j:ℝ) + 1) * θ) * (F (n - j) (n + 1) + F (n + 1) (n - j)) := by
      intro j hj
      have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [show n + 1 - j = n - j + 1 by omega, Finset.sum_range_succ,
        show n - j + j + 1 = n + 1 by omega]
      ring
    have hlast : ∑ j ∈ range (n + 1), Real.cos (((j:ℝ) + 1) * θ) *
          ∑ k ∈ range (n - j), (F k (k + j + 1) + F (k + j + 1) k) =
        ∑ j ∈ range n, Real.cos (((j:ℝ) + 1) * θ) *
          ∑ k ∈ range (n - j), (F k (k + j + 1) + F (k + j + 1) k) := by
      rw [Finset.sum_range_succ, Nat.sub_self, Finset.range_zero, Finset.sum_empty, mul_zero,
        add_zero]
    have hrefl : ∑ j ∈ range (n + 1), Real.cos (((j:ℝ) + 1) * θ) *
          (F (n - j) (n + 1) + F (n + 1) (n - j)) =
        ∑ k ∈ range (n + 1), (F k (n + 1) * Real.cos ((k:ℝ) * θ - ((n + 1 : ℕ):ℝ) * θ) +
          F (n + 1) k * Real.cos (((n + 1 : ℕ):ℝ) * θ - (k:ℝ) * θ)) := by
      rw [← Finset.sum_range_reflect (fun k => F k (n + 1) *
          Real.cos ((k:ℝ) * θ - ((n + 1 : ℕ):ℝ) * θ) +
          F (n + 1) k * Real.cos (((n + 1 : ℕ):ℝ) * θ - (k:ℝ) * θ)) (n + 1)]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      simp only [Nat.add_sub_cancel]
      rw [Nat.cast_sub hj']
      push_cast
      rw [show ((n:ℝ) - j) * θ - ((n:ℝ) + 1) * θ = -(((j:ℝ) + 1) * θ) by ring, Real.cos_neg,
        show ((n:ℝ) + 1) * θ - ((n:ℝ) - j) * θ = ((j:ℝ) + 1) * θ by ring]
      ring
    rw [hL, ih, ← hrefl, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hlast,
      Finset.sum_range_succ (fun k => F k k) (n + 1)]
    ring

lemma OSx_tele (ν β : ℝ) (m : ℕ) :
    2 * Real.sinh ν * ∑ k ∈ range m, Real.cosh (ν * (2 * (k:ℝ) + 1) + β) =
      Real.sinh (ν * (2 * (m:ℝ)) + β) - Real.sinh β := by
  rw [Finset.mul_sum]
  have h : ∀ k : ℕ, 2 * Real.sinh ν * Real.cosh (ν * (2 * (k:ℝ) + 1) + β) =
      Real.sinh (ν * (2 * ((k + 1 : ℕ):ℝ)) + β) - Real.sinh (ν * (2 * (k:ℝ)) + β) := by
    intro k
    push_cast
    rw [show ν * (2 * ((k:ℝ) + 1)) + β = (ν * (2 * (k:ℝ) + 1) + β) + ν by ring,
      show ν * (2 * (k:ℝ)) + β = (ν * (2 * (k:ℝ) + 1) + β) - ν by ring,
      Real.sinh_add, Real.sinh_sub]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k),
    Finset.sum_range_sub (fun k : ℕ => Real.sinh (ν * (2 * (k:ℝ)) + β)) m]
  simp

theorem solution (n : ℕ) (hn : 2 ≤ n) (lam : Rate) :
    Nonnegative (g n lam) := by
  intro θ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : (m + 1) - 1 = m := by omega
  unfold circle g fejer
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (if lam = ⊤ then 0 else if lam = 0 then
      1 - ((j + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) else
      Real.sinh (lam.toReal * (1 - ((j + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))) / Real.sinh lam.toReal) *
      Real.cos (((j + 1 : ℕ) : ℝ) * θ)) ((m + 1) - 1), hm1]
  by_cases htop : lam = ⊤
  · simp [htop]
  by_cases hzero : lam = 0
  · -- Fejér case
    have hq := OSx_quad (fun _ => 1) (m + 1) θ
    have hr := OSx_regroup (fun _ _ => (1:ℝ)) θ m
    simp only [one_mul, mul_one] at hq hr
    rw [hq] at hr
    have hpos : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    simp only [hzero, ENNReal.zero_ne_top, if_false, if_true]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hr
    have key : 1 + 2 * ∑ j ∈ range m, (1 - ((j + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) *
        Real.cos (((j + 1 : ℕ) : ℝ) * θ) =
        (((m + 1 : ℕ) : ℝ) + ∑ j ∈ range m, Real.cos (((j:ℝ) + 1) * θ) *
          (((m - j : ℕ) : ℝ) * (1 + 1))) / ((m + 1 : ℕ) : ℝ) := by
      rw [eq_div_iff hpos.ne', add_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j hj
        have hj' : j ≤ m := (Finset.mem_range.1 hj).le
        rw [Nat.cast_sub hj']
        push_cast
        field_simp
        try ring
    rw [key]
    apply div_nonneg _ hpos.le
    have := add_nonneg (sq_nonneg (∑ k ∈ range (m + 1), Real.cos ((k:ℝ) * θ)))
      (sq_nonneg (∑ k ∈ range (m + 1), Real.sin ((k:ℝ) * θ)))
    push_cast at hr ⊢
    linarith
  · -- hyperbolic case
    have hμ : 0 < lam.toReal := ENNReal.toReal_pos hzero htop
    set μ := lam.toReal with hμdef
    set N : ℝ := ((m + 1 : ℕ) : ℝ) with hN
    have hNpos : 0 < N := by rw [hN]; positivity
    set ν := μ / N with hν
    have hνpos : 0 < ν := div_pos hμ hNpos
    have hsν : 0 < Real.sinh ν := Real.sinh_pos_iff.2 hνpos
    have hsμ : 0 < Real.sinh μ := Real.sinh_pos_iff.2 hμ
    have hμν : μ = ν * N := by rw [hν]; field_simp
    let α : ℕ → ℝ := fun k => ν * ((k:ℝ) - (m:ℝ) / 2)
    have hq1 := OSx_quad (fun k => Real.cosh (α k)) (m + 1) θ
    have hq2 := OSx_quad (fun k => Real.sinh (α k)) (m + 1) θ
    have hr := OSx_regroup (fun k l => Real.cosh (α k + α l)) θ m
    have hsplitF : ∀ k l : ℕ, Real.cosh (α k + α l) =
        Real.cosh (α k) * Real.cosh (α l) + Real.sinh (α k) * Real.sinh (α l) :=
      fun k l => Real.cosh_add _ _
    have hD : 0 ≤ ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1),
        Real.cosh (α k + α l) * Real.cos ((k:ℝ) * θ - (l:ℝ) * θ) := by
      have e : ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1),
          Real.cosh (α k + α l) * Real.cos ((k:ℝ) * θ - (l:ℝ) * θ) =
          ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1),
            Real.cosh (α k) * Real.cosh (α l) * Real.cos ((k:ℝ) * θ - (l:ℝ) * θ) +
          ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1),
            Real.sinh (α k) * Real.sinh (α l) * Real.cos ((k:ℝ) * θ - (l:ℝ) * θ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro l _
        rw [hsplitF]; ring
      rw [e, hq1, hq2]
      positivity
    rw [hr] at hD
    -- diagonal
    have hdiag : ∑ k ∈ range (m + 1), Real.cosh (α k + α k) = Real.sinh μ / Real.sinh ν := by
      have t := OSx_tele ν (-(ν * N)) (m + 1)
      rw [eq_div_iff hsν.ne']
      have e : ∀ k ∈ range (m + 1), Real.cosh (α k + α k) =
          Real.cosh (ν * (2 * (k:ℝ) + 1) + -(ν * N)) := by
        intro k _
        congr 1
        simp only [α, hN]; push_cast; ring
      rw [Finset.sum_congr rfl e, hμν]
      have e2 : ν * (2 * ((m + 1 : ℕ) : ℝ)) + -(ν * N) = ν * N := by rw [hN]; ring
      rw [e2, Real.sinh_neg] at t
      linarith
    -- off-diagonal
    have hoff : ∀ j ∈ range m, ∑ k ∈ range (m - j), (Real.cosh (α k + α (k + j + 1)) +
        Real.cosh (α (k + j + 1) + α k)) =
        2 * (Real.sinh (μ * (1 - ((j + 1 : ℕ) : ℝ) / N)) / Real.sinh ν) := by
      intro j hj
      have hj' : j ≤ m := (Finset.mem_range.1 hj).le
      have t := OSx_tele ν (ν * ((j:ℝ) - m)) (m - j)
      have e : ∀ k ∈ range (m - j), Real.cosh (α k + α (k + j + 1)) +
          Real.cosh (α (k + j + 1) + α k) =
          2 * Real.cosh (ν * (2 * (k:ℝ) + 1) + ν * ((j:ℝ) - m)) := by
        intro k _
        rw [add_comm (α (k + j + 1)) (α k)]
        have : α k + α (k + j + 1) = ν * (2 * (k:ℝ) + 1) + ν * ((j:ℝ) - m) := by
          simp only [α]; push_cast; ring
        rw [this]; ring
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
      rw [Nat.cast_sub hj'] at t
      have e2 : ν * (2 * ((m:ℝ) - j)) + ν * ((j:ℝ) - m) = μ * (1 - ((j + 1 : ℕ) : ℝ) / N) := by
        rw [hμν]; field_simp; rw [hN]; push_cast; ring
      have e3 : ν * ((j:ℝ) - m) = -(μ * (1 - ((j + 1 : ℕ) : ℝ) / N)) := by
        rw [hμν]; field_simp; rw [hN]; push_cast; ring
      rw [e2, e3, Real.sinh_neg] at t
      rw [e3, mul_div_assoc', eq_div_iff hsν.ne']
      linarith
    rw [hdiag, Finset.sum_congr rfl (fun j hj => by rw [hoff j hj])] at hD
    simp only [htop, hzero, if_false]
    -- hD : 0 ≤ sinh μ / sinh ν + Σ cos * (2 * (sinh(..)/sinh ν))
    have key : 1 + 2 * ∑ j ∈ range m, Real.sinh (μ * (1 - ((j + 1 : ℕ) : ℝ) / N)) / Real.sinh μ *
        Real.cos (((j + 1 : ℕ) : ℝ) * θ) =
        (Real.sinh ν / Real.sinh μ) * (Real.sinh μ / Real.sinh ν +
          ∑ j ∈ range m, Real.cos (((j:ℝ) + 1) * θ) *
            (2 * (Real.sinh (μ * (1 - ((j + 1 : ℕ) : ℝ) / N)) / Real.sinh ν))) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · field_simp
      · apply Finset.sum_congr rfl
        intro j _
        push_cast
        field_simp
        try ring
    rw [key]
    exact mul_nonneg (div_nonneg hsν.le hsμ.le) hD

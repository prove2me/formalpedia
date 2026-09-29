-- Prove2me | solution 1 for TaoFivePrimes.sum_dirichlet_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T19:35:49.092661+00:00
-- url     : https://prove2.me/submissions/aa0a0464-5da2-4745-bf36-a20faf74bc7b

import Mathlib
open ArithmeticFunction Finset

/-- Summing a Dirichlet convolution of real arithmetic functions against a finitely
supported complex test function splits it into an outer and an inner sum. -/
theorem solution (a b : ArithmeticFunction ℝ) (F : ℕ → ℂ) (N : ℕ)
    (hF : ∀ n, N ≤ n → F n = 0) :
    ∑ n ∈ Finset.range N, (((a * b) n : ℝ) : ℂ) * F n
      = ∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ((a d : ℝ) : ℂ) * ((b m : ℝ) : ℂ) * F (d * m) := by
  classical
  set g : ℕ × ℕ → ℂ := fun p => ((a p.1 : ℝ) : ℂ) * ((b p.2 : ℝ) : ℂ) * F (p.1 * p.2) with hg
  have hRHS : ∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ((a d : ℝ) : ℂ) * ((b m : ℝ) : ℂ) * F (d * m)
      = ∑ p ∈ (Finset.range N) ×ˢ (Finset.range N), g p := by
    rw [Finset.sum_product]
  have hLHS : ∑ n ∈ Finset.range N, (((a * b) n : ℝ) : ℂ) * F n
      = ∑ p ∈ (Finset.range N).biUnion (fun n => n.divisorsAntidiagonal), g p := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hpn : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [hg]; simp only; rw [hpn]
    · intro i _ j _ hij
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hpi hpj
      have h1 := (Nat.mem_divisorsAntidiagonal.mp hpi).1
      have h2 := (Nat.mem_divisorsAntidiagonal.mp hpj).1
      exact hij (h1 ▸ h2 ▸ rfl)
  rw [hLHS, hRHS]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_range] at hp
    obtain ⟨n, hn, hpn⟩ := hp
    have hmem := Nat.mem_divisorsAntidiagonal.mp hpn
    have h1 : p.1 ≤ n := by
      rw [← hmem.1]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by
        rintro h; rw [h, mul_zero] at hmem; exact hmem.2 hmem.1.symm))
    have h2 : p.2 ≤ n := by
      rw [← hmem.1]
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (by
        rintro h; rw [h, zero_mul] at hmem; exact hmem.2 hmem.1.symm))
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt h1 hn),
      Finset.mem_range.mpr (lt_of_le_of_lt h2 hn)⟩
  · intro p hp hpn
    simp only [Finset.mem_biUnion, Finset.mem_range, not_exists] at hpn
    rw [hg]; simp only
    rcases Nat.eq_zero_or_pos p.1 with h1 | h1
    · rw [h1]; simp
    rcases Nat.eq_zero_or_pos p.2 with h2 | h2
    · rw [h2]; simp
    have hz : N ≤ p.1 * p.2 := by
      by_contra hc
      push_neg at hc
      exact (hpn (p.1 * p.2)) ⟨hc, Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, by positivity⟩⟩
    rw [hF _ hz]; ring

-- Prove2me | solution 1 for RobustDP.ChiSquare.eq51_gamma_elimination
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:39:34.331654+00:00
-- url     : https://prove2.me/submissions/0c47d703-3803-4b1d-9b51-2df18e2ee45f

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet

set_option autoImplicit false
open RobustDP.ChiSquare

theorem solution {S : Type*} [Fintype S] (q : S → ℝ)
    (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) (t : ℝ) (ht : 0 ≤ t) (v μ : S → ℝ) :
    IsGreatest ((fun γ : ℝ => expect q (v - μ) - Real.sqrt (t * ∑ s, q s * (v s - μ s - γ) ^ 2)) ''
        Set.univ)
      (dualObj q t v μ) ∧
    expect q (v - μ) - Real.sqrt (t * ∑ s, q s * (v s - μ s - expect q (v - μ)) ^ 2) =
      dualObj q t v μ := by
  have hsum1 : ∑ s, q s = 1 := hq.2
  have hdual : expect q (v - μ) - Real.sqrt (t * ∑ s, q s * (v s - μ s - expect q (v - μ)) ^ 2) =
      dualObj q t v μ := by
    simp only [dualObj, variance, Pi.sub_apply]
  refine ⟨⟨⟨expect q (v - μ), Set.mem_univ _, hdual⟩, ?_⟩, hdual⟩
  rintro _ ⟨γ, _, rfl⟩
  rw [← hdual]
  set E := expect q (v - μ) with hE
  have hEs : ∑ s, q s * (v s - μ s) = E := by
    simp only [hE, expect, Pi.sub_apply]
  have h : ∑ s, (q s * (v s - μ s - γ) ^ 2 - q s * (v s - μ s - E) ^ 2) = (E - γ) ^ 2 := by
    have : ∀ s, q s * (v s - μ s - γ) ^ 2 - q s * (v s - μ s - E) ^ 2 =
        (2 * (E - γ)) * (q s * (v s - μ s)) - ((E - γ) * (γ + E)) * q s := by
      intro s; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum1, hEs]
    ring
  have h2 : ∑ s, q s * (v s - μ s - E) ^ 2 ≤ ∑ s, q s * (v s - μ s - γ) ^ 2 := by
    rw [Finset.sum_sub_distrib] at h
    nlinarith [sq_nonneg (E - γ)]
  have h3 : Real.sqrt (t * ∑ s, q s * (v s - μ s - E) ^ 2) ≤
      Real.sqrt (t * ∑ s, q s * (v s - μ s - γ) ^ 2) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h2 ht)
  linarith

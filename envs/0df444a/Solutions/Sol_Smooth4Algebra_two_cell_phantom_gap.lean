-- Prove2me | solution 1 for Smooth4Algebra.two_cell_phantom_gap
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:01:33.854861+00:00
-- url     : https://prove2.me/submissions/9ed4a471-55c7-4355-a31b-e537206ff25f

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
set_option autoImplicit false

theorem solution
    (A C : ℤ →₀ ℕ) (hA : A ≠ 0)
    (gap : ℤ) (h_gap : 0 < gap)
    (h_forward : ∀ m : ℤ, A m = C (m - 1))
    (h_conjugate : ∀ m : ℤ, C m = A (m - (1 - 2 * gap))) :
    gap = 1 := by
  have h_shift : ∀ m : ℤ, A (m + (2 * gap - 2)) = A m := by
    intro m
    have hh := (h_forward m).trans (h_conjugate (m - 1))
    convert hh.symm using 1 <;> congr 1 <;> omega
  have h_period : 2 * gap - 2 = 0 := by
    classical
    have hs : A.support.Nonempty := Finsupp.support_nonempty_iff.mpr hA
    let M : ℤ := A.support.max' hs
    have hMmem : M ∈ A.support := Finset.max'_mem A.support hs
    have hM : A M ≠ 0 := Finsupp.mem_support_iff.mp hMmem
    have hplus : M + (2 * gap - 2) ∈ A.support :=
      Finsupp.mem_support_iff.mpr (by rw [h_shift]; exact hM)
    have hminus : M - (2 * gap - 2) ∈ A.support := by
      apply Finsupp.mem_support_iff.mpr
      have hh := h_shift (M - (2 * gap - 2))
      have hmk : M - (2 * gap - 2) + (2 * gap - 2) = M := by omega
      rw [hmk] at hh
      rw [← hh]
      exact hM
    have hp : M + (2 * gap - 2) ≤ M := Finset.le_max' A.support _ hplus
    have hm : M - (2 * gap - 2) ≤ M := Finset.le_max' A.support _ hminus
    omega
  omega


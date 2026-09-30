-- Prove2me | solution 1 for Smooth4Algebra.finite_support_shift_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:01:22.16671+00:00
-- url     : https://prove2.me/submissions/98cde80b-77e5-493f-92fb-9b43f4ed2110

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
set_option autoImplicit false

theorem solution
    {R : Type*} [Zero R] (f : ℤ →₀ R) (hf : f ≠ 0)
    (k : ℤ) (h_shift : ∀ m : ℤ, f (m + k) = f m) : k = 0 := by
  classical
  have hs : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  let M : ℤ := f.support.max' hs
  have hMmem : M ∈ f.support := Finset.max'_mem f.support hs
  have hM : f M ≠ 0 := Finsupp.mem_support_iff.mp hMmem
  have hplus : M + k ∈ f.support :=
    Finsupp.mem_support_iff.mpr (by rw [h_shift]; exact hM)
  have hminus : M - k ∈ f.support := by
    apply Finsupp.mem_support_iff.mpr
    have hh := h_shift (M - k)
    have hmk : M - k + k = M := by omega
    rw [hmk] at hh
    rw [← hh]
    exact hM
  have hp : M + k ≤ M := Finset.le_max' f.support _ hplus
  have hm : M - k ≤ M := Finset.le_max' f.support _ hminus
  omega


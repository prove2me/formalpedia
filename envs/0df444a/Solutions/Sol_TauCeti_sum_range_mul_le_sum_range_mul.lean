-- Prove2me | solution 1 for TauCeti.sum_range_mul_le_sum_range_mul
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:25:36.168819+00:00
-- url     : https://prove2.me/submissions/d73bee3d-babd-4bad-90e3-a07e7931caf1

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Comparing weighted sums through their partial sums

If every initial partial sum of `f` is at most the corresponding partial sum of `g`, then the
same comparison holds after weighting both sequences by a nonnegative, antitone weight `w`:
`∑_{i < N} w i * f i ≤ ∑_{i < N} w i * g i`. This is Abel's inequality in its comparison form.
Summation by parts (`Finset.sum_range_by_parts`) writes the difference of the two weighted sums
as the last weight times the last partial-sum difference plus the successive decrements of `w`
times the earlier partial-sum differences, and every one of these products is nonnegative.

No sign condition on `f` or `g` is needed. The typical use takes `g` constant: a bound
`∑_{i < k} f i ≤ k • C` on all partial sums then gives `∑ w i * f i ≤ (∑ w i) * C` for every
nonnegative antitone weight.

## Main results

* `TauCeti.sum_range_mul_le_sum_range_mul`: the weighted comparison.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Finset

variable {R : Type*} [Ring R] [Preorder R] [IsOrderedAddMonoid R] [PosMulMono R]

/-- **Abel's inequality, comparison form.** If the partial sums of `f` are dominated by those of
`g` up to `N`, and `w` is nonnegative and antitone on the first `N` indices, then
`∑_{i < N} w i * f i ≤ ∑_{i < N} w i * g i`. Only the last weight is required
to be nonnegative explicitly; the other signs follow from the successive comparisons
when `N > 0`. -/
theorem solution {f g w : ℕ → R} {N : ℕ}
    (hfg : ∀ k ≤ N, ∑ i ∈ _root_.Finset.range k, f i ≤ ∑ i ∈ _root_.Finset.range k, g i)
    (hw : ∀ i, i + 1 < N → w (i + 1) ≤ w i) (hw0 : 0 ≤ w (N - 1)) :
    ∑ i ∈ _root_.Finset.range N, w i * f i ≤ ∑ i ∈ _root_.Finset.range N, w i * g i := by
  set d : ℕ → R := fun i ↦ g i - f i with hd
  have hD : ∀ k ≤ N, 0 ≤ ∑ i ∈ _root_.Finset.range k, d i := fun k hk ↦ by
    simpa [hd, _root_.Finset.sum_sub_distrib] using hfg k hk
  suffices 0 ≤ ∑ i ∈ _root_.Finset.range N, w i * d i by
    simpa [hd, _root_.mul_sub, _root_.Finset.sum_sub_distrib] using this
  have hparts := _root_.Finset.sum_range_by_parts w d N
  simp only [_root_.smul_eq_mul] at hparts
  rw [hparts, _root_.sub_nonneg]
  calc ∑ i ∈ _root_.Finset.range (N - 1), (w (i + 1) - w i) * ∑ j ∈ _root_.Finset.range (i + 1), d j
      ≤ ∑ i ∈ _root_.Finset.range (N - 1), (0 : R) := by
        refine _root_.Finset.sum_le_sum fun i hi ↦ ?_
        rw [_root_.Finset.mem_range] at hi
        rw [← _root_.neg_sub (w i) (w (i + 1)), _root_.neg_mul]
        exact neg_nonpos.mpr (_root_.mul_nonneg (sub_nonneg.mpr (hw i (by omega)))
          (hD (i + 1) (by omega)))
    _ = 0 := _root_.Finset.sum_const_zero
    _ ≤ w (N - 1) * ∑ j ∈ _root_.Finset.range N, d j := _root_.mul_nonneg hw0 (hD N _root_.le_rfl)

end TauCeti

end
end

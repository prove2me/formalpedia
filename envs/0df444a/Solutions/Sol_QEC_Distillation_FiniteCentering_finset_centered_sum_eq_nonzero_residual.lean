-- Prove2me | solution 1 for QEC.Distillation.FiniteCentering.finset_centered_sum_eq_nonzero_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:57:37.100749+00:00
-- url     : https://prove2.me/submissions/bb98989f-f5ed-4f90-9007-ffd40bb5cce8

import Mathlib.Algebra.Module.BigOperators
import Definitions.Def_QEC_Distillation_Core_FiniteCentering

set_option autoImplicit false
universe u v w
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteCentering
open scoped BigOperators
namespace QEC.Distillation.FiniteCentering
theorem _root_.solution
    {ι : Type u} [DecidableEq ι] {R : Type v} [Semiring R] {M : Type w}
    [AddCommGroup M] [Module R M]
    (indices : Finset ι) (weight : ι → R) (accepts : ι → Prop)
    [DecidablePred accepts] (branch : ι → M) (zeroIndex : ι) (center : M)
    (hzero : branch zeroIndex = center) :
    (∑ i ∈ indices, if accepts i then weight i • branch i else 0) -
        (∑ i ∈ indices, if accepts i then weight i else 0) • center =
      ∑ i ∈ indices,
        if accepts i ∧ i ≠ zeroIndex then weight i • (branch i - center) else 0 := by
  rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : accepts i
  · by_cases hzeroIndex : i = zeroIndex
    · subst i
      simp [hi, hzero]
    · simpa [hi, hzeroIndex] using (smul_sub (weight i) (branch i) center).symm
  · simp [hi]
end QEC.Distillation.FiniteCentering

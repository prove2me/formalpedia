-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_exists_iterated_independent_linear_ideal_dimension_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/dafe7e8b-d229-4b8a-97dc-efaeab753fa3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_homogeneous_linear_slice_exists_independent_dimension_drop

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ))
    (c : Fin n → Fin m → ℂ)
    (hindependent : LinearIndependent ℂ c)
    (r : ℕ)
    (hdim : ringKrullDim
        (MvPolynomial (Fin m) ℂ ⧸
          permanentRolloutHomogeneousLinearSliceIdeal I c) ≤
      (r : WithBot ℕ∞)) :
    ∃ (q : ℕ) (d : Fin q → Fin m → ℂ),
      n ≤ q ∧ q ≤ n + r ∧ LinearIndependent ℂ d ∧
      ringKrullDim
        (MvPolynomial (Fin m) ℂ ⧸
          permanentRolloutHomogeneousLinearSliceIdeal I d) ≤
        (0 : WithBot ℕ∞) := by
  induction r generalizing n with
  | zero =>
      exact ⟨n, c, le_rfl, by omega, hindependent, hdim⟩
  | succ r ih =>
      by_cases hpositive :
          (0 : WithBot ℕ∞) <
            ringKrullDim
              (MvPolynomial (Fin m) ℂ ⧸
                permanentRolloutHomogeneousLinearSliceIdeal I c)
      · obtain ⟨x, hxindependent, hxdrop⟩ :=
          permanent_rollout_homogeneous_linear_slice_exists_independent_dimension_drop
            I hI c hindependent hpositive
        have hxbound :
            ringKrullDim
              (MvPolynomial (Fin m) ℂ ⧸
                permanentRolloutHomogeneousLinearSliceIdeal I (Fin.snoc c x)) ≤
              (r : WithBot ℕ∞) := by
          apply ENat.WithBot.add_le_add_one_right_iff.mp
          have hstep := hxdrop.trans hdim
          simpa [Nat.cast_add, Nat.cast_one] using hstep
        obtain ⟨q, d, hnq, hqbound, hdindependent, hdzero⟩ :=
          ih (Fin.snoc c x) hxindependent hxbound
        exact ⟨q, d, by omega, by omega, hdindependent, hdzero⟩
      · exact ⟨n, c, le_rfl, by omega, hindependent,
          le_of_not_gt hpositive⟩
end PermanentRollout

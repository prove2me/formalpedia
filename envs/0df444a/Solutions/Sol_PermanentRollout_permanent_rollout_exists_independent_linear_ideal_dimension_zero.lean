-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_exists_independent_linear_ideal_dimension_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/d149f78f-e3db-4131-9043-f1c6c74c1612

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_exists_iterated_independent_linear_ideal_dimension_zero

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
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ))
    (r : ℕ)
    (hdim : ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ I) ≤
      (r : WithBot ℕ∞)) :
    ∃ (q : ℕ) (c : Fin q → Fin m → ℂ),
      q ≤ r ∧ LinearIndependent ℂ c ∧
      ringKrullDim
        (MvPolynomial (Fin m) ℂ ⧸
          permanentRolloutHomogeneousLinearSliceIdeal I c) ≤
        (0 : WithBot ℕ∞) := by
  have hstart :
      ringKrullDim
        (MvPolynomial (Fin m) ℂ ⧸
          permanentRolloutHomogeneousLinearSliceIdeal I
            (Fin.elim0 : Fin 0 → Fin m → ℂ)) ≤
        (r : WithBot ℕ∞) := by
    change
      ringKrullDim
        (MvPolynomial (Fin m) ℂ ⧸
          (I ⊔ Ideal.span
            (Set.range fun j : Fin 0 =>
              permanentRolloutLinearCoordinateCombination m
                ((Fin.elim0 : Fin 0 → Fin m → ℂ) j)))) ≤
        (r : WithBot ℕ∞)
    rw [show Set.range (fun j : Fin 0 =>
      permanentRolloutLinearCoordinateCombination m
        ((Fin.elim0 : Fin 0 → Fin m → ℂ) j)) = ∅ by
      exact Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨j, _⟩ => Fin.elim0 j,
      Ideal.span_empty, sup_bot_eq]
    exact hdim
  obtain ⟨q, c, -, hq, hc, hzero⟩ :=
    permanent_rollout_exists_iterated_independent_linear_ideal_dimension_zero
      I hI (Fin.elim0 : Fin 0 → Fin m → ℂ)
      linearIndependent_empty_type r hstart
  exact ⟨q, c, by simpa using hq, hc, hzero⟩
end PermanentRollout

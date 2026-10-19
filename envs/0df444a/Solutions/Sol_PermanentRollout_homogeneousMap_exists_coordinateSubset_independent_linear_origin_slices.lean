-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_exists_coordinateSubset_independent_linear_origin_slices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/11fc5818-9b1e-46a9-a29c-6431b535b5df

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneous_eval_zero_of_pos
import Theorems.Thm_PermanentRollout_homogeneousIdeal_exists_independent_linear_origin_slices
import Theorems.Thm_PermanentRollout_homogeneousMap_coordinateSubset_quotient_ringKrullDim_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (coordinates : Finset (Fin k)) :
    ∃ c : Fin (k - coordinates.card) → Fin k → ℂ,
      LinearIndependent ℂ c ∧
      MvPolynomial.zeroLocus ℂ
        (homogeneousLinearSliceIdeal
          (Ideal.span (F '' (coordinates : Set (Fin k)))) c) =
        ({0} : Set (Fin k → ℂ)) := by
  classical
  let I : Ideal (MvPolynomial (Fin k) ℂ) :=
    Ideal.span (F '' (coordinates : Set (Fin k)))
  have hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) := by
    apply Ideal.homogeneous_span
    rintro _ ⟨i, _, rfl⟩
    exact ⟨e, hF i⟩
  have hproper : I ≠ ⊤ := by
    intro htop
    have hone : (1 : MvPolynomial (Fin k) ℂ) ∈ I := by
      simp [htop]
    have hcontain : I ≤
        RingHom.ker (MvPolynomial.eval (0 : Fin k → ℂ)) := by
      rw [show I = Ideal.span
        (F '' (coordinates : Set (Fin k))) by rfl,
        Ideal.span_le]
      rintro _ ⟨i, _, rfl⟩
      exact homogeneous_eval_zero_of_pos he (hF i)
    have hbad := hcontain hone
    simp at hbad
  have hdim :
      ringKrullDim (MvPolynomial (Fin k) ℂ ⧸ I) ≤
        ((k - coordinates.card : ℕ) : WithBot ℕ∞) := by
    simpa [I] using
      (homogeneousMap_coordinateSubset_quotient_ringKrullDim_le
        F e he hF hzero coordinates)
  exact homogeneousIdeal_exists_independent_linear_origin_slices
    I hI hproper (Nat.sub_le _ _) hdim
end PermanentRollout

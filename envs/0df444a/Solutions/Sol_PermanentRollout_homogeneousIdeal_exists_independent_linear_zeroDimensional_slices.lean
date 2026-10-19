-- Prove2me | solution 1 for PermanentRollout.homogeneousIdeal_exists_independent_linear_zeroDimensional_slices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/86e5bfb2-45cd-4c40-8b7a-d8ecdb449a06

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_exists_independent_zeroDimensional_extension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {t n : ℕ} (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (hlength : n ≤ t)
    (hdimension : ringKrullDim (MvPolynomial (Fin t) ℂ ⧸ I) ≤
      (↑n : WithBot ℕ∞)) :
    ∃ c : Fin n → Fin t → ℂ,
      LinearIndependent ℂ c ∧
        ringKrullDim
          (MvPolynomial (Fin t) ℂ ⧸ homogeneousLinearSliceIdeal I c) ≤
          (0 : WithBot ℕ∞) := by
  have hempty : homogeneousLinearSliceIdeal I
      (Fin.elim0 : Fin 0 → Fin t → ℂ) = I := by
    simp [homogeneousLinearSliceIdeal]
  have hbound : ringKrullDim
      (MvPolynomial (Fin t) ℂ ⧸
        homogeneousLinearSliceIdeal I
          (Fin.elim0 : Fin 0 → Fin t → ℂ)) ≤
        (↑n : WithBot ℕ∞) := by
    rwa [hempty]
  have hresult :=
    homogeneousLinearSliceIdeal_exists_independent_zeroDimensional_extension
      I hI (Fin.elim0 : Fin 0 → Fin t → ℂ)
      linearIndependent_empty_type n (by simpa using hlength) hbound
  rw [zero_add] at hresult
  exact hresult
end PermanentRollout

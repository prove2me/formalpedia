-- Prove2me | solution 1 for PermanentRollout.homogeneousIdeal_exists_independent_linear_origin_slices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/98c47e14-d689-458c-b906-c6a17c855901

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_leadingFormProjective_idealOfVars_isPrime
import Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousIdeal_exists_independent_linear_zeroDimensional_slices
import Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_le_idealOfVars
import Theorems.Thm_PermanentRollout_homogeneousIdeal_zeroLocus_eq_singleton_of_ringKrullDim_le_zero

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
    (hproper : I ≠ ⊤) (hlength : n ≤ t)
    (hdimension : ringKrullDim (MvPolynomial (Fin t) ℂ ⧸ I) ≤
      (↑n : WithBot ℕ∞)) :
    ∃ c : Fin n → Fin t → ℂ,
      LinearIndependent ℂ c ∧
        MvPolynomial.zeroLocus ℂ (homogeneousLinearSliceIdeal I c) =
          ({0} : Set (Fin t → ℂ)) := by
  obtain ⟨c, hc, hzero⟩ :=
    homogeneousIdeal_exists_independent_linear_zeroDimensional_slices
      I hI hlength hdimension
  refine ⟨c, hc, ?_⟩
  apply homogeneousIdeal_zeroLocus_eq_singleton_of_ringKrullDim_le_zero
  · exact homogeneousLinearSliceIdeal_isHomogeneous I hI c
  · intro htop
    have hvertex := homogeneousLinearSliceIdeal_le_idealOfVars
      I hI hproper c
    rw [htop] at hvertex
    exact (leadingFormProjective_idealOfVars_isPrime t).ne_top
      (top_unique hvertex)
  · exact hzero
end PermanentRollout

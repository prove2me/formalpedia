-- Prove2me | solution 1 for PermanentRollout.homogeneousIdeal_zeroLocus_eq_singleton_of_ringKrullDim_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/1b1ecb0f-4965-4247-b383-06543ce86b1c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_zeroLocus_idealOfVars
import Theorems.Thm_PermanentRollout_homogeneousIdeal_radical_eq_idealOfVars_of_ringKrullDim_le_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {t : ℕ} (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (hproper : I ≠ ⊤)
    (hdimension : ringKrullDim (MvPolynomial (Fin t) ℂ ⧸ I) ≤
      (0 : WithBot ℕ∞)) :
    MvPolynomial.zeroLocus ℂ I =
      ({0} : Set (Fin t → ℂ)) := by
  have hradical :=
    homogeneousIdeal_radical_eq_idealOfVars_of_ringKrullDim_le_zero
      I hI hproper hdimension
  calc
    MvPolynomial.zeroLocus ℂ I =
        MvPolynomial.zeroLocus ℂ I.radical := by
      apply le_antisymm
      · intro u hu f hf
        exact
          MvPolynomial.radical_le_vanishingIdeal_zeroLocus
            (K := ℂ) I hf u hu
      · exact MvPolynomial.zeroLocus_anti_mono I.le_radical
    _ = MvPolynomial.zeroLocus ℂ
          (MvPolynomial.idealOfVars (Fin t) ℂ) := by rw [hradical]
    _ = ({0} : Set (Fin t → ℂ)) := zeroLocus_idealOfVars
end PermanentRollout

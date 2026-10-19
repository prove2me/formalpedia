-- Prove2me | solution 1 for PermanentRollout.homogeneousIdeal_radical_eq_idealOfVars_of_ringKrullDim_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/f0c893c9-f7cb-4c56-9074-526898b5d9b9

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_leadingFormProjective_idealOfVars_isPrime
import Theorems.Thm_PermanentRollout_homogeneousIdeal_minimalPrime_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousPrime_le_idealOfVars

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
    I.radical = MvPolynomial.idealOfVars (Fin t) ℂ := by
  have hzero : Ring.KrullDimLE 0 (MvPolynomial (Fin t) ℂ ⧸ I) :=
    Ring.krullDimLE_iff.mpr hdimension
  have hallmaximal : ∀ P ∈ I.minimalPrimes, P.IsMaximal :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mp
      hzero
  have hvertexprime := leadingFormProjective_idealOfVars_isPrime t
  rw [← I.sInf_minimalPrimes]
  apply le_antisymm
  · obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_minimalPrimes hproper
    have hPhomogeneous :=
      homogeneousIdeal_minimalPrime_isHomogeneous I P hI hP
    have hPvertex :=
      homogeneousPrime_le_idealOfVars P hP.isPrime hPhomogeneous
    have hPeq : P = MvPolynomial.idealOfVars (Fin t) ℂ :=
      (hallmaximal P hP).eq_of_le hvertexprime.ne_top hPvertex
    rw [← hPeq]
    exact sInf_le hP
  · apply le_sInf
    intro P hP
    have hPhomogeneous :=
      homogeneousIdeal_minimalPrime_isHomogeneous I P hI hP
    have hPvertex :=
      homogeneousPrime_le_idealOfVars P hP.isPrime hPhomogeneous
    have hPeq : P = MvPolynomial.idealOfVars (Fin t) ℂ :=
      (hallmaximal P hP).eq_of_le hvertexprime.ne_top hPvertex
    exact hPeq.symm.le
end PermanentRollout

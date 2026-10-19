-- Prove2me | solution 1 for PermanentRollout.homogeneousIdeal_le_idealOfVars_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/513bf18e-e00a-4e69-ad20-019ac18cc0bb

import Mathlib
import Definitions.Def_Permanent
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
    (hproper : I ≠ ⊤) :
    I ≤ MvPolynomial.idealOfVars (Fin t) ℂ := by
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_minimalPrimes hproper
  exact hP.le.trans
    (homogeneousPrime_le_idealOfVars P hP.isPrime
      (homogeneousIdeal_minimalPrime_isHomogeneous I P hI hP))
end PermanentRollout

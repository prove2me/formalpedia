-- Prove2me | solution 1 for PermanentRollout.homogeneousPrime_le_idealOfVars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/125678f1-ccd1-4583-9b9f-c31f75340364

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    (P : Ideal (MvPolynomial (Fin t) ℂ)) (hP : P.IsPrime)
    (hhomogeneous : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ)) :
    P ≤ MvPolynomial.idealOfVars (Fin t) ℂ := by
  letI : P.IsPrime := hP
  intro p hp
  rw [← vanishingIdeal_origin_eq_idealOfVars,
    MvPolynomial.mem_vanishingIdeal_singleton_iff,
    MvPolynomial.aeval_zero]
  by_contra hconstant
  have hcomponent :
      MvPolynomial.homogeneousComponent 0 p ∈ P :=
    MvPolynomial.homogeneousComponent_mem_of_mem hhomogeneous hp 0
  rw [MvPolynomial.homogeneousComponent_zero] at hcomponent
  have hunit :
      IsUnit (MvPolynomial.C (MvPolynomial.coeff 0 p) :
        MvPolynomial (Fin t) ℂ) :=
    (isUnit_iff_ne_zero.mpr
      (by simpa [MvPolynomial.constantCoeff_eq] using hconstant)).map
        MvPolynomial.C
  exact (Ideal.notMem_of_isUnit P hunit) hcomponent
end PermanentRollout

-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_homogeneousPrime_le_idealOfVars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/12d2cbc7-2672-495f-bb5a-50f5eb02f398

import Mathlib
import Definitions.Def_Permanent

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
    {m : ℕ} (p : Ideal (MvPolynomial (Fin m) ℂ))
    (hprime : p.IsPrime)
    (hhomogeneous :
      p.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) ℂ)) :
    p ≤ MvPolynomial.idealOfVars (Fin m) ℂ := by
  letI : p.IsPrime := hprime
  intro f hf
  have hconstant : MvPolynomial.coeff 0 f = 0 := by
    by_contra hnonzero
    have hcomponent :
        MvPolynomial.homogeneousComponent 0 f ∈ p :=
      MvPolynomial.homogeneousComponent_mem_of_mem hhomogeneous hf 0
    rw [MvPolynomial.homogeneousComponent_zero] at hcomponent
    have hunit : IsUnit
        (MvPolynomial.C (MvPolynomial.coeff 0 f) :
          MvPolynomial (Fin m) ℂ) :=
      (isUnit_iff_ne_zero.mpr hnonzero).map MvPolynomial.C
    exact (Ideal.notMem_of_isUnit p hunit) hcomponent
  rw [← pow_one (MvPolynomial.idealOfVars (Fin m) ℂ),
    MvPolynomial.mem_pow_idealOfVars_iff']
  intro exponent hexponent
  have hezero : exponent = 0 :=
    (Finsupp.degree_eq_zero_iff exponent).mp
      (Nat.lt_one_iff.mp hexponent)
  simpa [hezero] using hconstant
end PermanentRollout

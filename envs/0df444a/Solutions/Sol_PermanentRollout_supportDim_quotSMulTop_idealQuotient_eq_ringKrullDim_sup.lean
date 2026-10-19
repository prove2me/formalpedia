-- Prove2me | solution 1 for PermanentRollout.supportDim_quotSMulTop_idealQuotient_eq_ringKrullDim_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/6b025ac4-d85b-4f9a-9242-d9887a73b53e

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    Module.supportDim R (QuotSMulTop x (R ⧸ I)) =
      ringKrullDim (R ⧸ (I ⊔ Ideal.span ({x} : Set R))) := by
  rw [Module.supportDim, Module.support_quotSMulTop,
    Module.support_eq_zeroLocus, Ideal.annihilator_quotient,
    ringKrullDim_quotient, PrimeSpectrum.zeroLocus_sup,
    PrimeSpectrum.zeroLocus_span]
end PermanentRollout

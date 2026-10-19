-- Prove2me | solution 1 for PermanentRollout.isSMulRegular_of_maximal_radical_and_regular_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/cee33664-c4d8-4d76-b8fa-c883bc0728b8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_isSMulRegular_iff_avoid_associatedPrimes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (g ell : R) (m : Ideal R)
    (hm : m.IsMaximal)
    (hrad : (I ⊔ Ideal.span ({g} : Set R)).radical = m)
    (hellm : ell ∈ m)
    (hellregular : IsSMulRegular (R ⧸ I) ell) :
    IsSMulRegular (R ⧸ I) g := by
  apply (isSMulRegular_iff_avoid_associatedPrimes g).mpr
  intro P hP hgP
  have hPassociated : IsAssociatedPrime P (R ⧸ I) := hP
  have hPprime : P.IsPrime := hPassociated.isPrime
  have hIP : I ≤ P := by
    have hann := hPassociated.annihilator_le
    simpa [Submodule.annihilator_top, Ideal.annihilator_quotient] using hann
  have hsupP : I ⊔ Ideal.span ({g} : Set R) ≤ P := by
    apply sup_le hIP
    exact Ideal.span_le.mpr (by simpa using hgP)
  have hmP : m ≤ P := by
    rw [← hrad]
    exact hPprime.radical_le_iff.mpr hsupP
  have heq : m = P := hm.eq_of_le hPprime.ne_top hmP
  have hellP : ell ∈ P := heq ▸ hellm
  exact ((isSMulRegular_iff_avoid_associatedPrimes ell).mp
    hellregular) P hP hellP
end PermanentRollout

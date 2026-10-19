-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_isSMulRegular_sup_of_quotient_map_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/a75ed302-ab61-4edd-8e36-a8b4b06c9c76

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommRing R]
    (I J : Ideal R) (g : R)
    (hregular : IsSMulRegular
      ((R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J))
      (Ideal.Quotient.mk J g)) :
    IsSMulRegular (R ⧸ (I ⊔ J)) g := by
  have hcolon :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem
      (I.map (Ideal.Quotient.mk J))
      (Ideal.Quotient.mk J g)).mp hregular
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (I ⊔ J) g).mpr
  intro p hp
  have hp' : g * p ∈ I ⊔ J := by simpa [smul_eq_mul] using hp
  have himage : Ideal.Quotient.mk J (g * p) ∈
      I.map (Ideal.Quotient.mk J) :=
    Ideal.mem_quotient_iff_mem_sup.mpr hp'
  have hproduct :
      Ideal.Quotient.mk J g • Ideal.Quotient.mk J p ∈
        (I.map (Ideal.Quotient.mk J) :
          Submodule (R ⧸ J) (R ⧸ J)) := by
    simpa [smul_eq_mul, map_mul] using himage
  have hmember := hcolon (Ideal.Quotient.mk J p) hproduct
  exact Ideal.mem_quotient_iff_mem_sup.mp hmember
end PermanentRollout

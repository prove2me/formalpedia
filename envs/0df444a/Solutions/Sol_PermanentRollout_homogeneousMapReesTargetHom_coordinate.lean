-- Prove2me | solution 1 for PermanentRollout.homogeneousMapReesTargetHom_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/df031452-4d22-4318-9bbd-c41f12984e8d

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
open scoped Pointwise BigOperators
open scoped BigOperators
open scoped Pointwise
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : ι → ℂ) (i : ι) :
    homogeneousMapReesTargetHom F e he hF hzero target
      (⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ :
        homogeneousMapSubalgebra F) =
      Polynomial.C (target i) * Polynomial.X ^ e := by
  let E := homogeneousMapCoordinateAlgEquiv F e he hF hzero
  have hE : E (MvPolynomial.X i) =
      (⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ :
        homogeneousMapSubalgebra F) := by
    apply Subtype.ext
    change MvPolynomial.aeval F (MvPolynomial.X i) = F i
    simp
  change (MvPolynomial.aeval fun q : ι =>
    Polynomial.C (target q) * Polynomial.X ^ e)
    (E.symm
      (⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ :
        homogeneousMapSubalgebra F)) = _
  rw [← hE, E.symm_apply_apply, MvPolynomial.aeval_X]
end PermanentRollout

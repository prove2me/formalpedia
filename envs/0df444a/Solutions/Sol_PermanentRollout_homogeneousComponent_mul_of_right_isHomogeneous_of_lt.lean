-- Prove2me | solution 1 for PermanentRollout.homogeneousComponent_mul_of_right_isHomogeneous_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/a2af444f-927d-471d-b889-026584385fe7

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} (g f : MvPolynomial ι ℂ) {e n : ℕ}
    (hf : f.IsHomogeneous e) (hn : n < e) :
    MvPolynomial.homogeneousComponent n (g * f) = 0 := by
  have hcomponent (q : MvPolynomial ι ℂ) (j : ℕ) :
      (DirectSum.decompose
        (MvPolynomial.homogeneousSubmodule ι ℂ) q j :
          MvPolynomial ι ℂ) = MvPolynomial.homogeneousComponent j q := by
    change
      (((inferInstance : DirectSum.Decomposition
        (MvPolynomial.homogeneousSubmodule ι ℂ)).decompose' q j :
          MvPolynomial ι ℂ)) = _
    rw [show (inferInstance : DirectSum.Decomposition
      (MvPolynomial.homogeneousSubmodule ι ℂ)) =
        MvPolynomial.decomposition from Subsingleton.elim _ _]
    exact MvPolynomial.decomposition.decompose'_apply q j
  have hprojection :=
    DirectSum.coe_decompose_mul_of_right_mem_of_not_le
      (𝒜 := MvPolynomial.homogeneousSubmodule ι ℂ)
      (a := g) (b := f) (n := n) (i := e) hf (by omega)
  simpa only [hcomponent] using hprojection
end PermanentRollout

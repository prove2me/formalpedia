-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_degreeSupport_eq_antidiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/659a56d8-4e68-4d21-9538-a07b08e62694

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
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    {d : ι →₀ ℕ | d.degree = n} =
      (((Finset.univ : Finset ι).finsuppAntidiag n : Finset (ι →₀ ℕ)) :
        Set (ι →₀ ℕ)) := by
  classical
  ext d
  simp [Finsupp.degree_eq_sum]
end PermanentRollout

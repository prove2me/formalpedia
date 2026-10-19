-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_sourcePrefix_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/ae11fa1e-21b0-4fd0-9f91-4ad84e2f77ba

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
namespace PermanentRollout
theorem _root_.solution
    {k j : ℕ} (hj : j < k) :
    homogeneousMapAllKSourcePrefix k (j + 1) =
      insert (⟨j, hj⟩ : Fin k) (homogeneousMapAllKSourcePrefix k j) := by
  ext i
  simp only [homogeneousMapAllKSourcePrefix, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hi
    by_cases heq : i.val = j
    · exact Or.inl (Fin.ext heq)
    · exact Or.inr (by omega)
  · intro hi
    rcases hi with hi | hi
    · subst i
      simp
    · omega
end PermanentRollout

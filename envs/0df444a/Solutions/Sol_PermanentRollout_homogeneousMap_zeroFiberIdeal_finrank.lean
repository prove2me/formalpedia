-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_zeroFiberIdeal_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/8329d31b-56aa-4c96-bb6a-dd4c71e32b65

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_zeroFiberIdeal_finrank_of_pos_rank

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
namespace PermanentRollout
theorem _root_.solution
    (k : ℕ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    Module.finrank ℂ
      (MvPolynomial (Fin k) ℂ ⧸ homogeneousMapIdeal F) = e ^ k := by
  classical
  cases k with
  | zero =>
      have hI : homogeneousMapIdeal F =
          (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) := by
        simp [homogeneousMapIdeal]
      rw [hI]
      calc
        Module.finrank ℂ
            (MvPolynomial (Fin 0) ℂ ⧸
              (⊥ : Ideal (MvPolynomial (Fin 0) ℂ))) =
            Module.finrank ℂ (MvPolynomial (Fin 0) ℂ) :=
          (Submodule.quotEquivOfEqBot _ rfl).finrank_eq
        _ = Module.finrank ℂ ℂ :=
          (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).toLinearEquiv.finrank_eq
        _ = e ^ 0 := by simp
  | succ k =>
      exact homogeneousMap_zeroFiberIdeal_finrank_of_pos_rank
        (k + 1) (Nat.zero_lt_succ k) F e he hF hzero
end PermanentRollout

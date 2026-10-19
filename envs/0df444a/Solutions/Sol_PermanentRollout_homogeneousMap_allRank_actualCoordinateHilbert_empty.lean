-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_actualCoordinateHilbert_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/9f8cebfa-fc36-4bbe-bf92-988f83fd7191

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_homogeneousSubmodule_finrank
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_coordinateSubsetIdeal_empty

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
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ) (n : ℕ) :
    homogeneousMapAllKActualCoordinateHilbert F ∅ n =
      (k + n - 1).choose n := by
  classical
  letI : Module.Finite ℂ
      (MvPolynomial.homogeneousSubmodule (Fin k) ℂ n) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin k) ℂ n)
  have hpiece :
      homogeneousMapGradedIdealPiece
        (homogeneousMapAllKCoordinateSubsetIdeal F ∅) n = ⊥ := by
    rw [homogeneousMap_allRank_coordinateSubsetIdeal_empty]
    ext p
    change ((p : MvPolynomial (Fin k) ℂ) ∈
      (⊥ : Ideal (MvPolynomial (Fin k) ℂ))) ↔
      p ∈ (⊥ : Submodule ℂ
        (MvPolynomial.homogeneousSubmodule (Fin k) ℂ n))
    simp
  unfold homogeneousMapAllKActualCoordinateHilbert
  calc
    Module.finrank ℂ
        (homogeneousMapGradedQuotientPiece
          (homogeneousMapAllKCoordinateSubsetIdeal F ∅) n) =
        Module.finrank ℂ
          (MvPolynomial.homogeneousSubmodule (Fin k) ℂ n ⧸
            (⊥ : Submodule ℂ
              (MvPolynomial.homogeneousSubmodule (Fin k) ℂ n))) :=
      (Submodule.quotEquivOfEq _ _ hpiece).finrank_eq
    _ = Module.finrank ℂ
        (MvPolynomial.homogeneousSubmodule (Fin k) ℂ n) :=
      (Submodule.quotEquivOfEqBot _ rfl).finrank_eq
    _ = (k + n - 1).choose n := by
      simpa using
        (homogeneousMap_homogeneousSubmodule_finrank (ι := Fin k) n)
end PermanentRollout

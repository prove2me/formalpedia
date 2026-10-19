-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_sourcePrefix_isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/b9417486-b4f5-427a-98cf-1a64869a7f8f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_coordinatePolynomials_isWeaklyRegular
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_sourcePrefix_ofList

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
    (k : ℕ) (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (j : ℕ) (hj : j < k) :
    IsSMulRegular
      (MvPolynomial (Fin k) ℂ ⧸
        Ideal.span (F ''
          (homogeneousMapAllKSourcePrefix k j : Set (Fin k))))
      (F ⟨j, hj⟩) := by
  classical
  have hweak :=
    homogeneousMap_coordinatePolynomials_isWeaklyRegular
      k F e he hF hzero
  have hlength : j < (List.ofFn F).length := by
    simpa only [List.length_ofFn] using hj
  have hreg := hweak.regular_mod_prev j hlength
  have hsub :
      (Ideal.ofList ((List.ofFn F).take j) •
        (⊤ : Submodule (MvPolynomial (Fin k) ℂ)
          (MvPolynomial (Fin k) ℂ))) =
        (Ideal.span (F ''
          (homogeneousMapAllKSourcePrefix k j : Set (Fin k))) :
          Submodule (MvPolynomial (Fin k) ℂ)
            (MvPolynomial (Fin k) ℂ)) := by
    rw [homogeneousMap_allRank_sourcePrefix_ofList F j]
    simp
  apply ((Submodule.quotEquivOfEq _ _ hsub).isSMulRegular_congr
    (F ⟨j, hj⟩)).mp
  simpa only [List.getElem_ofFn] using hreg
end PermanentRollout

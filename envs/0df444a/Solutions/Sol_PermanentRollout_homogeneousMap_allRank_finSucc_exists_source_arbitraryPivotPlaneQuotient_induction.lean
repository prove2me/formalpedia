-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_finSucc_exists_source_arbitraryPivotPlaneQuotient_induction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/84df1ea4-fe65-4b7a-af56-acb829c714f2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMapFinSucc_exists_source_arbitraryPivot_restricted_zeroFiber
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_finSucc_arbitraryPivotPlaneQuotientEquiv_mk_eq_aeval

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
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ}
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin (n + 1) → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    ∃ (c : Fin (n + 1) → ℂ) (j : Fin (n + 1)) (hj : c j ≠ 0),
      (∀ i : Fin n,
        (homogeneousMapFinSuccArbitraryPivotPlaneQuotientEquiv c j hj
          (Ideal.Quotient.mk
            (Ideal.span
              ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
                Set (MvPolynomial (Fin (n + 1)) ℂ)))
            (F i.castSucc))).IsHomogeneous e) ∧
      (∀ u : Fin n → ℂ,
        (∀ i : Fin n,
          MvPolynomial.eval u
            (homogeneousMapFinSuccArbitraryPivotPlaneQuotientEquiv c j hj
              (Ideal.Quotient.mk
                (Ideal.span
                  ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
                    Set (MvPolynomial (Fin (n + 1)) ℂ)))
                (F i.castSucc))) = 0) ↔ u = 0) := by
  obtain ⟨c, j, hj, hhom, horigin⟩ :=
    homogeneousMapFinSucc_exists_source_arbitraryPivot_restricted_zeroFiber
      F e he hF hzero
  refine ⟨c, j, hj, ?_, ?_⟩
  · intro i
    rw [homogeneousMap_allRank_finSucc_arbitraryPivotPlaneQuotientEquiv_mk_eq_aeval]
    exact hhom i
  · intro u
    simpa only [homogeneousMap_allRank_finSucc_arbitraryPivotPlaneQuotientEquiv_mk_eq_aeval]
      using horigin u
end PermanentRollout

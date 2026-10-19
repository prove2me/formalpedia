-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_coordinatePolynomials_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/f42dfe3e-c875-4ce4-8c9c-322df15eed5a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanentRolloutLinearCoordinateCombination_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_finSucc_exists_source_arbitraryPivotPlaneQuotient_induction
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_homogeneous_fin_isWeaklyRegular_of_linear_quotient_aux
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_ringEquiv_isWeaklyRegular_ofFn_image
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_finSucc_lastCoordinate_isSMulRegular_of_slice_weaklyRegular

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
namespace PermanentRollout
theorem _root_.solution
    (k : ℕ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin k) ℂ) (List.ofFn F) := by
  induction k with
  | zero =>
      exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
  | succ n ih =>
      obtain ⟨c, j, hj, hhom, hrestrictedZero⟩ :=
        homogeneousMap_allRank_finSucc_exists_source_arbitraryPivotPlaneQuotient_induction
          F e he hF hzero
      let ell : MvPolynomial (Fin (n + 1)) ℂ :=
        permanentRolloutLinearCoordinateCombination (n + 1) c
      let J : Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
        Ideal.span ({ell} : Set (MvPolynomial (Fin (n + 1)) ℂ))
      let q : MvPolynomial (Fin (n + 1)) ℂ →+*
          MvPolynomial (Fin (n + 1)) ℂ ⧸ J := Ideal.Quotient.mk J
      let E := homogeneousMapFinSuccArbitraryPivotPlaneQuotientEquiv c j hj
      let G : Fin n → MvPolynomial (Fin n) ℂ :=
        fun i => E (q (F i.castSucc))
      have hGhom : ∀ i, (G i).IsHomogeneous e := hhom
      have hGzero : ∀ u : Fin n → ℂ,
          (∀ i, MvPolynomial.eval u (G i) = 0) ↔ u = 0 :=
        hrestrictedZero
      have hGweak : RingTheory.Sequence.IsWeaklyRegular
          (MvPolynomial (Fin n) ℂ) (List.ofFn G) :=
        ih G hGhom hGzero
      have hQweak : RingTheory.Sequence.IsWeaklyRegular
          (MvPolynomial (Fin (n + 1)) ℂ ⧸ J)
          (List.ofFn fun i : Fin n => q (F i.castSucc)) := by
        apply homogeneousMap_allRank_ringEquiv_isWeaklyRegular_ofFn_image
          E.toRingEquiv (fun i : Fin n => q (F i.castSucc))
        exact hGweak
      have hell : ell ≠ 0 := by
        intro hz
        have hev := congrArg
          (MvPolynomial.eval (Pi.single j (1 : ℂ))) hz
        apply hj
        simpa [ell, permanentRolloutLinearCoordinateCombination,
          Pi.single_apply, mul_ite] using hev
      have hellhom : ell.IsHomogeneous 1 :=
        permanentRolloutLinearCoordinateCombination_isHomogeneous c
      have hprefix : RingTheory.Sequence.IsWeaklyRegular
          (MvPolynomial (Fin (n + 1)) ℂ)
          (List.ofFn fun i : Fin n => F i.castSucc) := by
        exact homogeneousMap_allRank_homogeneous_fin_isWeaklyRegular_of_linear_quotient_aux
          ell hell hellhom n (fun i : Fin n => F i.castSucc)
          (fun i => hF i.castSucc) hQweak
      have hlast : IsSMulRegular
          (MvPolynomial (Fin (n + 1)) ℂ ⧸
            Ideal.span (Set.range fun i : Fin n => F i.castSucc))
          (F (Fin.last n)) :=
        homogeneousMap_allRank_finSucc_lastCoordinate_isSMulRegular_of_slice_weaklyRegular
          F hzero c j hj hQweak
      rw [List.ofFn_succ_last,
        RingTheory.Sequence.isWeaklyRegular_append_iff,
        RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      refine ⟨hprefix, ?_⟩
      have hspan :
          Ideal.ofList (List.ofFn fun i : Fin n => F i.castSucc) =
            Ideal.span (Set.range fun i : Fin n => F i.castSucc) := by
        change Ideal.span {p | p ∈ List.ofFn
          (fun i : Fin n => F i.castSucc)} = _
        congr 1
        ext p
        simp
      have hsub :
          (Ideal.ofList (List.ofFn fun i : Fin n => F i.castSucc) •
            (⊤ : Submodule (MvPolynomial (Fin (n + 1)) ℂ)
              (MvPolynomial (Fin (n + 1)) ℂ))) =
            (Ideal.span (Set.range fun i : Fin n => F i.castSucc) :
              Submodule (MvPolynomial (Fin (n + 1)) ℂ)
                (MvPolynomial (Fin (n + 1)) ℂ)) := by
        simp [hspan]
      exact ((Submodule.quotEquivOfEq _ _ hsub).isSMulRegular_congr
        (F (Fin.last n))).mpr hlast
end PermanentRollout

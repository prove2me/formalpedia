-- Prove2me | solution 1 for QEC.Coding.ReedMuller.evaluation_pairing_eq_zero_of_add_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:56:44.490824+00:00
-- url     : https://prove2.me/submissions/48e67616-3593-4df4-aa64-36f33e7861fb

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace ReedMuller
open scoped BigOperators
private theorem monomialValue_eq_fullProduct {m r : Nat}
    (monomial : SquarefreeMonomial m r) (point : BooleanPoint m) :
    monomialValue monomial point =
      ∏ coordinate : Fin m,
        if coordinate ∈ monomial.1 then point coordinate else 1 := by
  classical
  simp [monomialValue]
private theorem monomial_pairing_zero {m r s : Nat}
    (left : SquarefreeMonomial m r) (right : SquarefreeMonomial m s)
    (hdegree : r + s < m) :
    ∑ point : BooleanPoint m,
      monomialValue left point * monomialValue right point = 0 := by
  classical
  have hunionCard : (left.1 ∪ right.1).card < m := by
    calc
      (left.1 ∪ right.1).card ≤ left.1.card + right.1.card :=
        Finset.card_union_le _ _
      _ ≤ r + s := Nat.add_le_add left.2 right.2
      _ < m := hdegree
  have hunion : left.1 ∪ right.1 ≠ Finset.univ := by
    intro heq
    have hcard : (left.1 ∪ right.1).card = m := by
      rw [heq]
      simp
    omega
  obtain ⟨free, hfree⟩ : ∃ free : Fin m, free ∉ left.1 ∪ right.1 := by
    by_contra hnone
    apply hunion
    apply Finset.eq_univ_of_forall
    intro coordinate
    by_contra hcoordinate
    exact hnone ⟨coordinate, hcoordinate⟩
  have hfreeLeft : free ∉ left.1 := by
    exact fun hmem => hfree (Finset.mem_union_left _ hmem)
  have hfreeRight : free ∉ right.1 := by
    exact fun hmem => hfree (Finset.mem_union_right _ hmem)
  calc
    ∑ point : BooleanPoint m,
        monomialValue left point * monomialValue right point =
        ∑ point : BooleanPoint m,
          ∏ coordinate : Fin m,
            ((if coordinate ∈ left.1 then point coordinate else 1) *
              (if coordinate ∈ right.1 then point coordinate else 1)) := by
          apply Finset.sum_congr rfl
          intro point _hpoint
          rw [monomialValue_eq_fullProduct, monomialValue_eq_fullProduct,
            ← Finset.prod_mul_distrib]
    _ = ∏ coordinate : Fin m, ∑ bit : ZMod 2,
          ((if coordinate ∈ left.1 then bit else 1) *
            (if coordinate ∈ right.1 then bit else 1)) := by
          rw [Fintype.prod_sum]
    _ = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ free)
          simp [hfreeLeft, hfreeRight]
          exact ZMod.natCast_self 2
private theorem evaluation_eq_sum_basis {m r : Nat}
    (polynomial : ANFPolynomial m r) :
    evaluationLinearMap m r polynomial =
      ∑ monomial, polynomial monomial •
        evaluationLinearMap m r (basisPolynomial monomial) := by
  classical
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext target
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Fintype.sum_eq_single target]
  · simp [basisPolynomial, canonicalBasisWord]
  · intro other hne
    simp [basisPolynomial, canonicalBasisWord, hne]
end ReedMuller
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators
namespace QEC.Coding.ReedMuller
theorem _root_.solution {m r s : Nat}
    (hdegree : r + s < m)
    (left : ANFPolynomial m r) (right : ANFPolynomial m s) :
    wordPairing (evaluationLinearMap m r left)
      (evaluationLinearMap m s right) = 0 := by
  classical
  rw [evaluation_eq_sum_basis, evaluation_eq_sum_basis]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro rightMonomial _hright
  rw [show (∑ leftMonomial,
      left leftMonomial •
        wordPairing
          (evaluationLinearMap m r (basisPolynomial leftMonomial))
          (evaluationLinearMap m s (basisPolynomial rightMonomial))) = 0 by
    apply Finset.sum_eq_zero
    intro leftMonomial _hleft
    have hpair :
        wordPairing
          (evaluationLinearMap m r (basisPolynomial leftMonomial))
          (evaluationLinearMap m s (basisPolynomial rightMonomial)) = 0 := by
      change
        (∑ point,
          evaluationLinearMap m r (basisPolynomial leftMonomial) point *
            evaluationLinearMap m s (basisPolynomial rightMonomial) point) = 0
      simp_rw [evaluation_basisPolynomial]
      exact monomial_pairing_zero leftMonomial rightMonomial hdegree
    rw [hpair]
    simp]
  simp
end QEC.Coding.ReedMuller

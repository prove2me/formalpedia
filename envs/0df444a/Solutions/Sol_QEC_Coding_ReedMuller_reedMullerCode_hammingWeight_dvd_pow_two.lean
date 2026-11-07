-- Prove2me | solution 1 for QEC.Coding.ReedMuller.reedMullerCode_hammingWeight_dvd_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:56:52.238989+00:00
-- url     : https://prove2.me/submissions/aa52c55a-5778-4f9b-b07e-7c33f06ebd30

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
private theorem monomialValue_eq_supportValue {m r : Nat}
    (monomial : SquarefreeMonomial m r) (point : BooleanPoint m) :
    monomialValue monomial point = supportValue monomial.1 point :=
  rfl
private theorem supportValue_union {m : Nat}
    (left right : Finset (Fin m)) (point : BooleanPoint m) :
    supportValue left point * supportValue right point =
      supportValue (left ∪ right) point := by
  classical
  unfold supportValue
  have hinter : left ∩ right ⊆ left ∪ right := by
    intro coordinate hcoordinate
    exact Finset.mem_union_left _ (Finset.mem_of_mem_inter_left hcoordinate)
  calc
    (∏ coordinate ∈ left, point coordinate) *
        ∏ coordinate ∈ right, point coordinate =
        (∏ coordinate ∈ left ∪ right, point coordinate) *
          ∏ coordinate ∈ left ∩ right, point coordinate :=
      (Finset.prod_union_inter (f := fun coordinate : Fin m => point coordinate)).symm
    _ = ((∏ coordinate ∈ (left ∪ right) \ (left ∩ right), point coordinate) *
          ∏ coordinate ∈ left ∩ right, point coordinate) *
            ∏ coordinate ∈ left ∩ right, point coordinate := by
      rw [Finset.prod_sdiff hinter]
    _ = (∏ coordinate ∈ (left ∪ right) \ (left ∩ right), point coordinate) *
          ∏ coordinate ∈ left ∩ right, point coordinate := by
      have hidempotent :
          (∏ coordinate ∈ left ∩ right, point coordinate) *
              ∏ coordinate ∈ left ∩ right, point coordinate =
            ∏ coordinate ∈ left ∩ right, point coordinate := by
        have hpoint : ∀ coordinate : Fin m,
            point coordinate * point coordinate = point coordinate := by
          intro coordinate
          by_cases hzero : point coordinate = 0
          · simp [hzero]
          · rw [binary_eq_one_of_ne_zero _ hzero]
            norm_num
        calc
          (∏ coordinate ∈ left ∩ right, point coordinate) *
              ∏ coordinate ∈ left ∩ right, point coordinate =
              ∏ coordinate ∈ left ∩ right,
                point coordinate * point coordinate := by
            rw [← Finset.prod_mul_distrib]
          _ = ∏ coordinate ∈ left ∩ right, point coordinate := by
            apply Finset.prod_congr rfl
            intro coordinate _hcoordinate
            exact hpoint coordinate
      rw [mul_assoc, hidempotent]
    _ = ∏ coordinate ∈ left ∪ right, point coordinate :=
      Finset.prod_sdiff hinter
private theorem supportValue_ne_zero_iff {m : Nat}
    (support : Finset (Fin m)) (point : BooleanPoint m) :
    supportValue support point ≠ 0 ↔ support ⊆ hammingSupport point := by
  rw [supportValue, Finset.prod_ne_zero_iff]
  constructor
  · intro h coordinate hcoordinate
    simpa [hammingSupport] using h coordinate hcoordinate
  · intro h coordinate hcoordinate
    simpa [hammingSupport] using h hcoordinate
private theorem hammingWeight_supportValue {m : Nat}
    (support : Finset (Fin m)) :
    HammingWeight (supportValue support : Word (ZMod 2) (BooleanPoint m)) =
      2 ^ (m - support.card) := by
  classical
  rw [HammingWeight, hammingSupport]
  calc
    ((Finset.univ : Finset (BooleanPoint m)).filter
        fun point => supportValue support point ≠ 0).card =
        Fintype.card {point : BooleanPoint m //
          support ⊆ hammingSupport point} := by
            rw [Fintype.card_subtype]
            congr 1
            ext point
            simp [supportValue_ne_zero_iff]
    _ = Fintype.card
        (Word (ZMod 2) {coordinate : Fin m // coordinate ∉ support}) :=
      Fintype.card_congr (constrainedPointEquiv support)
    _ = 2 ^ (m - support.card) := by
      rw [Fintype.card_fun]
      simp [ZMod.card]
private theorem hammingWeight_add_two_mul_binaryOverlap {m : Nat}
    (left right : Word (ZMod 2) (BooleanPoint m)) :
    HammingWeight left + HammingWeight right =
      HammingWeight (left + right) + 2 * binaryOverlap left right := by
  classical
  have hpoint : ∀ point : BooleanPoint m,
      (if left point ≠ 0 then 1 else 0) + (if right point ≠ 0 then 1 else 0) =
        (if left point + right point ≠ 0 then 1 else 0) +
          2 * (if left point * right point ≠ 0 then 1 else 0) := by
    intro point
    by_cases hleft : left point = 0
    · simp [hleft]
    · rw [binary_eq_one_of_ne_zero _ hleft]
      by_cases hright : right point = 0
      · simp [hright]
      · rw [binary_eq_one_of_ne_zero _ hright]
        decide
  have hsum := Finset.sum_congr rfl
    (fun point (_hpoint : point ∈ (Finset.univ : Finset (BooleanPoint m))) =>
      hpoint point)
  simp only [HammingWeight, hammingSupport, Finset.card_filter, binaryOverlap]
  rw [← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  simpa only [Pi.add_apply] using hsum
private theorem restrictedEvaluation_cons {m r : Nat}
    (support : Finset (Fin m)) (monomial : SquarefreeMonomial m r)
    (tail : List (SquarefreeMonomial m r)) :
    restrictedEvaluation support (monomial :: tail) =
      supportValue (support ∪ monomial.1) + restrictedEvaluation support tail := by
  funext point
  simp only [restrictedEvaluation, List.map_cons, List.sum_cons, Pi.add_apply]
  rw [mul_add, monomialValue_eq_supportValue, supportValue_union]
private theorem binaryOverlap_restrictedEvaluation_supportValue {m r : Nat}
    (support : Finset (Fin m)) (monomial : SquarefreeMonomial m r)
    (tail : List (SquarefreeMonomial m r)) :
    binaryOverlap (supportValue (support ∪ monomial.1))
      (restrictedEvaluation support tail) =
        HammingWeight (restrictedEvaluation (support ∪ monomial.1) tail) := by
  unfold binaryOverlap
  congr 1
  funext point
  simp only [restrictedEvaluation]
  calc
    supportValue (support ∪ monomial.1) point *
        (supportValue support point *
          (tail.map fun other => monomialValue other point).sum) =
        (supportValue (support ∪ monomial.1) point * supportValue support point) *
          (tail.map fun other => monomialValue other point).sum := by ring
    _ = supportValue (support ∪ monomial.1) point *
          (tail.map fun other => monomialValue other point).sum := by
      rw [supportValue_union]
      have hunion : (support ∪ monomial.1) ∪ support =
          support ∪ monomial.1 := by
        ext coordinate
        simp only [Finset.mem_union]
        tauto
      rw [hunion]
private theorem restrictedEvaluation_hammingWeight_dvd_pow_two
    {m r : Nat} (hr : 0 < r) :
    ∀ (nu : Nat) (support : Finset (Fin m))
      (monomials : List (SquarefreeMonomial m r)),
      support.card + nu * r < m →
        2 ^ nu ∣ HammingWeight (restrictedEvaluation support monomials) := by
  intro nu
  induction nu with
  | zero =>
      intro support monomials _hbound
      simp
  | succ nu ih =>
      intro support monomials hbound
      induction monomials with
      | nil =>
          rw [show restrictedEvaluation support [] = 0 by
            funext point
            simp [restrictedEvaluation]]
          simp
      | cons monomial tail ihtail =>
          have htail :
              2 ^ (nu + 1) ∣ HammingWeight (restrictedEvaluation support tail) :=
            ihtail
          have hunionBound : (support ∪ monomial.1).card + nu * r < m := by
            have hcard : (support ∪ monomial.1).card ≤ support.card + r := by
              calc
                (support ∪ monomial.1).card ≤ support.card + monomial.1.card :=
                  Finset.card_union_le _ _
                _ ≤ support.card + r := Nat.add_le_add_left monomial.2 _
            rw [Nat.succ_mul] at hbound
            omega
          have hoverlap :
              2 ^ nu ∣ HammingWeight
                (restrictedEvaluation (support ∪ monomial.1) tail) :=
            ih (support ∪ monomial.1) tail hunionBound
          have hheadExponent : nu + 1 ≤ m - (support ∪ monomial.1).card := by
            have hcard : (support ∪ monomial.1).card ≤ support.card + r := by
              calc
                (support ∪ monomial.1).card ≤ support.card + monomial.1.card :=
                  Finset.card_union_le _ _
                _ ≤ support.card + r := Nat.add_le_add_left monomial.2 _
            have hmul : nu ≤ nu * r := Nat.le_mul_of_pos_right nu hr
            rw [Nat.succ_mul] at hbound
            omega
          have hhead :
              2 ^ (nu + 1) ∣ HammingWeight
                (supportValue (support ∪ monomial.1)) := by
            rw [hammingWeight_supportValue]
            exact pow_dvd_pow 2 hheadExponent
          have htwiceOverlap :
              2 ^ (nu + 1) ∣
                2 * binaryOverlap (supportValue (support ∪ monomial.1))
                  (restrictedEvaluation support tail) := by
            rw [binaryOverlap_restrictedEvaluation_supportValue]
            simpa only [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
              (Nat.mul_dvd_mul_left 2 hoverlap)
          have hsum :
              2 ^ (nu + 1) ∣
                HammingWeight (supportValue (support ∪ monomial.1)) +
                  HammingWeight (restrictedEvaluation support tail) :=
            hhead.add htail
          have hidentity :
              HammingWeight (restrictedEvaluation support (monomial :: tail)) +
                2 * binaryOverlap (supportValue (support ∪ monomial.1))
                  (restrictedEvaluation support tail) =
                HammingWeight (supportValue (support ∪ monomial.1)) +
                  HammingWeight (restrictedEvaluation support tail) := by
            rw [restrictedEvaluation_cons]
            simpa [Nat.add_comm] using
              (hammingWeight_add_two_mul_binaryOverlap
                (supportValue (support ∪ monomial.1))
                (restrictedEvaluation support tail)).symm
          rw [← hidentity] at hsum
          exact (Nat.dvd_add_iff_left htwiceOverlap).2 hsum
private theorem evaluation_eq_restrictedEvaluation_activeMonomials {m r : Nat}
    (polynomial : ANFPolynomial m r) :
    evaluationLinearMap m r polynomial =
      restrictedEvaluation ∅ (activeMonomials polynomial) := by
  classical
  funext point
  simp only [evaluationLinearMap_apply, restrictedEvaluation, supportValue,
    Finset.prod_empty, one_mul, activeMonomials]
  rw [Finset.sum_map_toList]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro monomial _hmonomial
  by_cases hzero : polynomial monomial = 0
  · simp [hzero]
  · have hone : polynomial monomial = 1 :=
      binary_eq_one_of_ne_zero _ hzero
    simp [hone]
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
theorem _root_.solution {nu r m : Nat}
    (hr : 0 < r) (hnu : nu * r < m)
    {word : Word (ZMod 2) (BooleanPoint m)}
    (hword : word ∈ (reedMullerCode r m).carrier) :
    2 ^ nu ∣ HammingWeight word := by
  rcases (mem_reedMullerCode word).1 hword with ⟨polynomial, hpolynomial⟩
  rw [← hpolynomial, evaluation_eq_restrictedEvaluation_activeMonomials]
  simpa using restrictedEvaluation_hammingWeight_dvd_pow_two hr nu ∅
    (activeMonomials polynomial) (by simpa using hnu)
end QEC.Coding.ReedMuller

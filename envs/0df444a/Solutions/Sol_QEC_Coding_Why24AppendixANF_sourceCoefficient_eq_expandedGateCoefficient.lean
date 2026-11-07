-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_eq_expandedGateCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:41:20.845769+00:00
-- url     : https://prove2.me/submissions/9a3a354f-c3d0-4f4d-99f6-e8b107bb0d6b

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_singleton
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.Why24BooleanANF.evaluate_generator
attribute [local simp] QEC.Coding.Why24BooleanANF.generator_mul_self
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC.Coding.Why24AppendixANF
open scoped BigOperators
private theorem expandedGateCoefficient_eq_contributions
    (support : Finset (Fin 10)) :
    expandedGateCoefficient support = linearContribution support +
      pairContribution support + tripleContribution support :=
  rfl
private theorem orderedPair_eq {first second left right : Fin 10}
    (hfirst : first < second) (hleft : left < right)
    (hsupport : {left, right} = ({first, second} : Finset (Fin 10))) :
    left = first ∧ right = second := by
  have hleftMem : left = first ∨ left = second := by
    have : left ∈ ({first, second} : Finset (Fin 10)) := by
      rw [← hsupport]
      simp
    simpa using this
  have hrightMem : right = first ∨ right = second := by
    have : right ∈ ({first, second} : Finset (Fin 10)) := by
      rw [← hsupport]
      simp
    simpa using this
  rcases hleftMem with h | h <;> rcases hrightMem with h' | h' <;>
    subst_vars <;> omega
private theorem orderedTriple_eq
    {first second third left middle right : Fin 10}
    (hfirst : first < second) (hsecond : second < third)
    (hleft : left < middle) (hmiddle : middle < right)
    (hsupport : {left, middle, right} =
      ({first, second, third} : Finset (Fin 10))) :
    left = first ∧ middle = second ∧ right = third := by
  have hleftMem : left = first ∨ left = second ∨ left = third := by
    have : left ∈ ({first, second, third} : Finset (Fin 10)) := by
      rw [← hsupport]
      simp
    simpa using this
  have hmiddleMem : middle = first ∨ middle = second ∨ middle = third := by
    have : middle ∈ ({first, second, third} : Finset (Fin 10)) := by
      rw [← hsupport]
      simp
    simpa using this
  have hrightMem : right = first ∨ right = second ∨ right = third := by
    have : right ∈ ({first, second, third} : Finset (Fin 10)) := by
      rw [← hsupport]
      simp
    simpa using this
  rcases hleftMem with h | h | h <;>
    rcases hmiddleMem with h' | h' | h' <;>
    rcases hrightMem with h'' | h'' | h'' <;>
    subst_vars <;> omega
private theorem linearContribution_eq_zero_of_card_ne_one
    (support : Finset (Fin 10)) (hcard : support.card ≠ 1) :
    linearContribution support = 0 := by
  classical
  unfold linearContribution
  apply Finset.sum_eq_zero
  intro coordinate _
  rw [if_neg]
  intro hsupport
  apply hcard
  rw [← hsupport]
  simp
private theorem linearContribution_singleton (coordinate : Fin 10) :
    linearContribution {coordinate} = 1 := by
  classical
  unfold linearContribution
  rw [Fintype.sum_eq_single coordinate]
  · simp
  · intro other hne
    rw [if_neg]
    intro hsupport
    apply hne
    simpa only [Finset.singleton_inj] using hsupport
private theorem pairContribution_eq_zero_of_card_ne_two
    (support : Finset (Fin 10)) (hcard : support.card ≠ 2) :
    pairContribution support = 0 := by
  classical
  unfold pairContribution
  apply Finset.sum_eq_zero
  intro left _
  apply Finset.sum_eq_zero
  intro right _
  rw [if_neg]
  intro h
  apply hcard
  rw [← h.2]
  exact Finset.card_pair h.1.ne
private theorem pairContribution_pair (left right : Fin 10)
    (hlt : left < right) :
    pairContribution {left, right} = quadraticGateCoefficient left right := by
  classical
  unfold pairContribution
  rw [Fintype.sum_eq_single left]
  · rw [Fintype.sum_eq_single right]
    · simp [hlt]
    · intro candidate hne
      rw [if_neg]
      intro h
      exact hne (orderedPair_eq hlt h.1 h.2).2
  · intro candidate hne
    apply Finset.sum_eq_zero
    intro other _
    rw [if_neg]
    intro h
    exact hne (orderedPair_eq hlt h.1 h.2).1
private theorem tripleContribution_eq_zero_of_card_ne_three
    (support : Finset (Fin 10)) (hcard : support.card ≠ 3) :
    tripleContribution support = 0 := by
  classical
  unfold tripleContribution
  apply Finset.sum_eq_zero
  intro first _
  apply Finset.sum_eq_zero
  intro second _
  apply Finset.sum_eq_zero
  intro third _
  rw [if_neg]
  intro h
  apply hcard
  rw [← h.2.2]
  exact Finset.card_triple_eq_three_iff.mpr
    ⟨h.1.ne, (h.1.trans h.2.1).ne, h.2.1.ne⟩
private theorem tripleContribution_triple (first second third : Fin 10)
    (hfirst : first < second) (hsecond : second < third) :
    tripleContribution {first, second, third} =
      cubicGateCoefficient first second third := by
  classical
  unfold tripleContribution
  rw [Fintype.sum_eq_single first]
  · rw [Fintype.sum_eq_single second]
    · rw [Fintype.sum_eq_single third]
      · simp [hfirst, hsecond]
      · intro candidate hne
        rw [if_neg]
        intro h
        exact hne (orderedTriple_eq hfirst hsecond h.1 h.2.1 h.2.2).2.2
    · intro candidate hne
      apply Finset.sum_eq_zero
      intro other _
      rw [if_neg]
      intro h
      exact hne (orderedTriple_eq hfirst hsecond h.1 h.2.1 h.2.2).2.1
  · intro candidate hne
    apply Finset.sum_eq_zero
    intro middle _
    apply Finset.sum_eq_zero
    intro right _
    rw [if_neg]
    intro h
    exact hne (orderedTriple_eq hfirst hsecond h.1 h.2.1 h.2.2).1
private theorem sourceCoefficient_empty : sourceCoefficient ∅ = 0 := by
  unfold sourceCoefficient
  apply Finset.sum_eq_zero
  intro first _
  apply Finset.sum_eq_zero
  intro second _
  apply Finset.sum_eq_zero
  intro third _
  simp [tripleSupport]
private theorem sourceCoefficient_eq_zero_of_three_lt_card
    (support : Finset (Fin 10)) (hcard : 3 < support.card) :
    sourceCoefficient support = 0 := by
  unfold sourceCoefficient
  apply Finset.sum_eq_zero
  intro first _
  apply Finset.sum_eq_zero
  intro second _
  apply Finset.sum_eq_zero
  intro third _
  rw [if_neg]
  intro hsupport
  have hcardEq := congrArg Finset.card hsupport
  have hle : (tripleSupport first second third).card ≤ 3 := by
    simpa only [tripleSupport] using
      (Finset.card_le_three (a := first) (b := second) (c := third))
  omega
private theorem support_eq_sorted_pair (support : Finset (Fin 10))
    (hcard : support.card = 2) :
    support =
      {support.orderEmbOfFin hcard (0 : Fin 2),
        support.orderEmbOfFin hcard (1 : Fin 2)} := by
  calc
    support = Finset.image (support.orderEmbOfFin hcard) Finset.univ :=
      (Finset.image_orderEmbOfFin_univ support hcard).symm
    _ = _ := by
      rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl]
      simp
private theorem support_eq_sorted_triple (support : Finset (Fin 10))
    (hcard : support.card = 3) :
    support =
      {support.orderEmbOfFin hcard (0 : Fin 3),
        support.orderEmbOfFin hcard (1 : Fin 3),
        support.orderEmbOfFin hcard (2 : Fin 3)} := by
  calc
    support = Finset.image (support.orderEmbOfFin hcard) Finset.univ :=
      (Finset.image_orderEmbOfFin_univ support hcard).symm
    _ = _ := by
      rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} from rfl]
      simp
end QEC.Coding.Why24AppendixANF
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution
    (support : Finset (Fin 10)) :
    sourceCoefficient support = expandedGateCoefficient support := by
  rw [expandedGateCoefficient_eq_contributions]
  by_cases hzero : support.card = 0
  · have hs : support = ∅ := Finset.card_eq_zero.mp hzero
    subst support
    rw [sourceCoefficient_empty,
      linearContribution_eq_zero_of_card_ne_one ∅ (by simp),
      pairContribution_eq_zero_of_card_ne_two ∅ (by simp),
      tripleContribution_eq_zero_of_card_ne_three ∅ (by simp)]
    simp
  by_cases hone : support.card = 1
  · obtain ⟨coordinate, rfl⟩ := Finset.card_eq_one.mp hone
    rw [sourceCoefficient_singleton, linearContribution_singleton,
      pairContribution_eq_zero_of_card_ne_two _ (by simp),
      tripleContribution_eq_zero_of_card_ne_three _ (by simp)]
    simp
  by_cases htwo : support.card = 2
  · let left := support.orderEmbOfFin htwo (0 : Fin 2)
    let right := support.orderEmbOfFin htwo (1 : Fin 2)
    have hlt : left < right :=
      (support.orderEmbOfFin htwo).strictMono (by decide)
    have hs : support = {left, right} := support_eq_sorted_pair support htwo
    rw [hs]
    change sourcePairCoefficient left right = _
    rw [sourceCoefficient_pair left right hlt,
      linearContribution_eq_zero_of_card_ne_one _ (by
        have hcard := Finset.card_pair hlt.ne
        omega),
      pairContribution_pair left right hlt,
      tripleContribution_eq_zero_of_card_ne_three _ (by
        have hcard := Finset.card_pair hlt.ne
        omega)]
    simp
  by_cases hthree : support.card = 3
  · let first := support.orderEmbOfFin hthree (0 : Fin 3)
    let second := support.orderEmbOfFin hthree (1 : Fin 3)
    let third := support.orderEmbOfFin hthree (2 : Fin 3)
    have hfirst : first < second :=
      (support.orderEmbOfFin hthree).strictMono (by decide)
    have hsecond : second < third :=
      (support.orderEmbOfFin hthree).strictMono (by decide)
    have hs : support = {first, second, third} :=
      support_eq_sorted_triple support hthree
    rw [hs]
    change sourceTripleCoefficient first second third = _
    rw [sourceCoefficient_triple first second third hfirst hsecond,
      linearContribution_eq_zero_of_card_ne_one _ (by
        have hcard := Finset.card_triple_eq_three_iff.mpr
          ⟨hfirst.ne, (hfirst.trans hsecond).ne, hsecond.ne⟩
        omega),
      pairContribution_eq_zero_of_card_ne_two _ (by
        have hcard := Finset.card_triple_eq_three_iff.mpr
          ⟨hfirst.ne, (hfirst.trans hsecond).ne, hsecond.ne⟩
        omega),
      tripleContribution_triple first second third hfirst hsecond]
    simp
  have hlarge : 3 < support.card := by omega
  rw [sourceCoefficient_eq_zero_of_three_lt_card support hlarge,
    linearContribution_eq_zero_of_card_ne_one support hone,
    pairContribution_eq_zero_of_card_ne_two support htwo,
    tripleContribution_eq_zero_of_card_ne_three support hthree]
  simp
end QEC.Coding.Why24AppendixANF

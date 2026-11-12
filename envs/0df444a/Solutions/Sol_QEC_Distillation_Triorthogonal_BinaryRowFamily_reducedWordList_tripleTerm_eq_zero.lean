-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedWordList_tripleTerm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:26:42.067254+00:00
-- url     : https://prove2.me/submissions/46aebcc0-ba2e-4318-9f33-8aa883fc150e

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRow_triple_even
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRowIndexList_nodup
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_tripleOverlap_cast
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
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


attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
section
noncomputable section
namespace QEC
namespace Distillation
namespace Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
namespace CliffordCorrectionAtom
end CliffordCorrectionAtom
universe uO uE uC
namespace BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
private theorem tripleOverlap_smul_even
    {x y z : Word (ZMod 2) Col} (hx hy hz : ZMod 2)
    (h : Even (tripleOverlap x y z)) :
    Even (tripleOverlap (hx • x) (hy • y) (hz • z)) := by
  rw [← ZMod.natCast_eq_zero_iff_even, tripleOverlap_cast]
  have hzero : (∑ p, x p * y p * z p) = 0 := by
    rw [← tripleOverlap_cast]
    exact ZMod.natCast_eq_zero_iff_even.mpr h
  calc
    ∑ p, (hx • x) p * (hy • y) p * (hz • z) p =
        hx * hy * hz * ∑ p, x p * y p * z p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
    _ = 0 := by rw [hzero, mul_zero]
private theorem four_mul_natCast8_eq_zero_of_even
    {n : Nat} (h : Even n) : (4 : ZMod 8) * (n : ZMod 8) = 0 := by
  rcases h with ⟨k, rfl⟩
  rw [Nat.cast_add]
  ring_nf
  have h8 : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
  simp [h8]
private theorem four_mul_fixedPairTripleSum8_eq_zero
    {A : Type*} [DecidableEq A]
    (v : A → Word (ZMod 2) Col) (c : A → ZMod 2)
    (r s : A) (rs : List A)
    (hrs : r ≠ s) (hr : r ∉ rs) (hs : s ∉ rs)
    (htriple : ∀ {r s t : A}, r ≠ s → r ≠ t → s ≠ t →
      Even (tripleOverlap (v r) (v s) (v t))) :
    (4 : ZMod 8) * fixedPairTripleSum8 (c r • v r) (c s • v s)
      (rs.map fun t => c t • v t) = 0 := by
  induction rs with
  | nil => simp [fixedPairTripleSum8]
  | cons t ts ih =>
      have hrt : r ≠ t := by
        intro hrt
        apply hr
        simp [hrt]
      have hst : s ≠ t := by
        intro hst
        apply hs
        simp [hst]
      have hrts : r ∉ ts := by
        intro hmem
        exact hr (by simp [hmem])
      have hsts : s ∉ ts := by
        intro hmem
        exact hs (by simp [hmem])
      have hterm :
          (4 : ZMod 8) *
            (tripleOverlap (c r • v r) (c s • v s) (c t • v t) : ZMod 8) = 0 :=
        four_mul_natCast8_eq_zero_of_even
          (tripleOverlap_smul_even (c r) (c s) (c t)
            (htriple hrs hrt hst))
      simp only [List.map_cons, fixedPairTripleSum8, mul_add]
      rw [hterm, ih hrts hsts, add_zero]
private theorem four_mul_fixedTripleSum8_eq_zero
    {A : Type*} [DecidableEq A]
    (v : A → Word (ZMod 2) Col) (c : A → ZMod 2)
    (r : A) (rs : List A) (hr : r ∉ rs) (hnd : rs.Nodup)
    (htriple : ∀ {r s t : A}, r ≠ s → r ≠ t → s ≠ t →
      Even (tripleOverlap (v r) (v s) (v t))) :
    (4 : ZMod 8) * fixedTripleSum8 (c r • v r)
      (rs.map fun s => c s • v s) = 0 := by
  induction rs with
  | nil => simp [fixedTripleSum8]
  | cons s ss ih =>
      have hrs : r ≠ s := by
        intro hrs
        apply hr
        simp [hrs]
      have hrss : r ∉ ss := by
        intro hmem
        exact hr (by simp [hmem])
      have hsss : s ∉ ss := (List.nodup_cons.mp hnd).1
      have hndss : ss.Nodup := (List.nodup_cons.mp hnd).2
      simp only [List.map_cons, fixedTripleSum8, mul_add]
      rw [four_mul_fixedPairTripleSum8_eq_zero v c r s ss hrs hrss hsss htriple,
        ih hrss hndss, add_zero]
private theorem four_mul_wordTripleSum8_eq_zero
    {A : Type*} [DecidableEq A]
    (v : A → Word (ZMod 2) Col) (c : A → ZMod 2)
    (rs : List A) (hnd : rs.Nodup)
    (htriple : ∀ {r s t : A}, r ≠ s → r ≠ t → s ≠ t →
      Even (tripleOverlap (v r) (v s) (v t))) :
    (4 : ZMod 8) * wordTripleSum8 (rs.map fun r => c r • v r) = 0 := by
  induction rs with
  | nil => simp [wordTripleSum8]
  | cons r rs ih =>
      have hr : r ∉ rs := (List.nodup_cons.mp hnd).1
      have hndrs : rs.Nodup := (List.nodup_cons.mp hnd).2
      simp only [List.map_cons, wordTripleSum8, mul_add]
      rw [four_mul_fixedTripleSum8_eq_zero v c r rs hr hndrs htriple,
        ih hndrs, add_zero]
universe v
end BinaryRowFamily
end Triorthogonal
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    (4 : ZMod 8) * wordTripleSum8 (R.reducedWordList c) = 0 := by
  exact four_mul_wordTripleSum8_eq_zero R.reducedRow c R.reducedRowIndexList
    R.reducedRowIndexList_nodup
      (fun hrs hrt hst => R.reducedRow_triple_even hR hrs hrt hst)
end QEC.Distillation.Triorthogonal.BinaryRowFamily

-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_evenCode_evenCode_rowCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:15:13.148265+00:00
-- url     : https://prove2.me/submissions/90b225b9-b306-4961-b3e8-d610a8aee4ea

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_eq_cast
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_add_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_smul_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_swap_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_rotate
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_self_left
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
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordPairing_evenCode_rowCode
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
private theorem wordTriplePairing_span_left
    {A : Type*} (v : A → Word (ZMod 2) Col)
    (y z : Word (ZMod 2) Col)
    (h : ∀ i, wordTriplePairing (v i) y z = 0)
    {x : Word (ZMod 2) Col}
    (hx : x ∈ Submodule.span (ZMod 2) (Set.range v)) :
    wordTriplePairing x y z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact h i
  | zero => simp
  | add x x' _ _ hx hx' =>
      rw [wordTriplePairing_add_left, hx, hx', add_zero]
  | smul c x _ hx =>
      rw [wordTriplePairing_smul_left, hx, mul_zero]
private theorem wordTriplePairing_eq_zero_of_even
    {x y z : Word (ZMod 2) Col}
    (h : Even (tripleOverlap x y z)) :
    wordTriplePairing x y z = 0 := by
  rw [wordTriplePairing_eq_cast]
  exact ZMod.natCast_eq_zero_iff_even.mpr h
private theorem evenRow_evenRow_row_triplePairing
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (b₁ b₂ : EvenRow) (r : Sum OddRow EvenRow) :
    wordTriplePairing (R.evenRow b₁) (R.evenRow b₂) (R.row r) = 0 := by
  by_cases h₁₂ : b₁ = b₂
  · subst b₂
    rw [wordTriplePairing_self_left]
    exact R.wordPairing_evenCode_rowCode hR
      (R.evenRow_mem_evenCode b₁) (R.row_mem_rowCode r)
  · rcases r with a | b₃
    · apply wordTriplePairing_eq_zero_of_even
      exact hR.triple_even (.inr b₁) (.inr b₂) (.inl a)
        (by simpa using h₁₂) (by simp) (by simp)
    · by_cases h₁₃ : b₁ = b₃
      · subst b₃
        change wordTriplePairing (R.evenRow b₁) (R.evenRow b₂)
          (R.evenRow b₁) = 0
        rw [wordTriplePairing_rotate, wordTriplePairing_self_left,
          R.evenRow_pairing hR]
      · by_cases h₂₃ : b₂ = b₃
        · subst b₃
          change wordTriplePairing (R.evenRow b₁) (R.evenRow b₂)
            (R.evenRow b₂) = 0
          rw [wordTriplePairing_swap_left, wordTriplePairing_rotate,
            wordTriplePairing_self_left, R.evenRow_pairing hR]
        · apply wordTriplePairing_eq_zero_of_even
          exact hR.triple_even (.inr b₁) (.inr b₂) (.inr b₃)
            (by simpa using h₁₂) (by simpa using h₁₃)
              (by simpa using h₂₃)
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
    {x y z : Word (ZMod 2) Col}
    (hx : x ∈ R.evenCode.carrier) (hy : y ∈ R.evenCode.carrier)
    (hz : z ∈ R.rowCode.carrier) : wordTriplePairing x y z = 0 := by
  apply wordTriplePairing_span_left R.evenRow y z (fun b₁ => ?_) hx
  rw [wordTriplePairing_swap_left]
  apply wordTriplePairing_span_left R.evenRow (R.evenRow b₁) z
    (fun b₂ => ?_) hy
  rw [wordTriplePairing_rotate]
  apply wordTriplePairing_span_left R.row (R.evenRow b₂) (R.evenRow b₁)
    (fun r => ?_) hz
  simpa only [wordTriplePairing_rotate] using
    (evenRow_evenRow_row_triplePairing R hR b₂ b₁ r)
end QEC.Distillation.Triorthogonal.BinaryRowFamily

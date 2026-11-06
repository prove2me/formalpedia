-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:07:00.619272+00:00
-- url     : https://prove2.me/submissions/fdda66aa-7812-4348-b9df-1472126e5838

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toQubitOperator_eq_binaryDagger
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryMul
import Theorems.Thm_QEC_Coding_StabilizerCode_detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
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


attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
section
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
open scoped ComplexConjugate
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem inner_toQubitOperator_pair_eq_relative
    (A B : Binary ι) (x y : Semantics.Qubit.QubitRegister ι) :
    inner Complex (toQubitOperator A x) (toQubitOperator B y) =
      inner Complex x (toQubitOperator (binaryMul (binaryDagger A) B) y) := by
  classical
  calc
    inner Complex (toQubitOperator A x) (toQubitOperator B y) =
        inner Complex x
          (LinearMap.adjoint (toQubitOperator A) (toQubitOperator B y)) := by
      simpa using
        (LinearMap.adjoint_inner_right (𝕜 := Complex) (toQubitOperator A) x
          (toQubitOperator B y)).symm
    _ = inner Complex x (toQubitOperator (binaryMul (binaryDagger A) B) y) := by
      rw [adjoint_toQubitOperator_eq_binaryDagger, toQubitOperator_binaryMul]
      rfl
end PauliSymplectic
namespace StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
end StabilizerCode
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    {α : Type v} [Fintype α]
    (Q : SourceValidBinary ι) (E : α → Binary ι) (amp : α → Complex) :
    (binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion Q.1.code ↔
      ∀ a b, amp a ≠ 0 → amp b ≠ 0 →
        Q.1.InGeneratedGroupUpToSign
            (binaryMul (binaryDagger (E a)) (E b)) ∨
          ¬ Q.1.InBinaryNormalizer
            (binaryMul (binaryDagger (E a)) (E b)) := by
  classical
  constructor
  · intro hKL
    rcases
        ((binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
          Q.1.code).1 hKL with
      ⟨scalar, hscalar⟩
    intro a b ha hb
    apply
      (detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
        Q (binaryMul (binaryDagger (E a)) (E b))).1
    refine ⟨scalar a b / (star (amp a) * amp b), ?_⟩
    intro x hx y hy
    have hscale_ne : star (amp a) * amp b ≠ 0 :=
      mul_ne_zero (star_ne_zero.mpr ha) hb
    have hab := hscalar a b x hx y hy
    have hscaled :
        (star (amp a) * amp b) *
            inner Complex x
              (toQubitOperator (binaryMul (binaryDagger (E a)) (E b)) y) =
          scalar a b * inner Complex x y := by
      calc
        (star (amp a) * amp b) *
              inner Complex x
                (toQubitOperator (binaryMul (binaryDagger (E a)) (E b)) y) =
            inner Complex
              ((binaryPauliKrausFamily E amp).operator a x)
              ((binaryPauliKrausFamily E amp).operator b y) := by
                rw [binaryPauliKrausFamily_operator, binaryPauliKrausFamily_operator]
                rw [← inner_toQubitOperator_pair_eq_relative]
                simp
                ring
        _ = scalar a b * inner Complex x y := hab
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hscale_ne).2
    simpa [mul_comm] using hscaled
  · intro hpairs
    have hscalarExists :
        ∀ a b : α, ∃ c : Complex,
          amp a ≠ 0 → amp b ≠ 0 →
            Semantics.DetectableOnWithScalar Q.1.code
              (toQubitOperator (binaryMul (binaryDagger (E a)) (E b))) c := by
      intro a b
      by_cases ha : amp a = 0
      · exact ⟨0, fun ha' _ => False.elim (ha' ha)⟩
      by_cases hb : amp b = 0
      · exact ⟨0, fun _ hb' => False.elim (hb' hb)⟩
      rcases
          (detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
            Q (binaryMul (binaryDagger (E a)) (E b))).2 (hpairs a b ha hb) with
        ⟨c, hc⟩
      exact ⟨c, fun _ _ => hc⟩
    choose scalar hscalar using hscalarExists
    rw [(binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
      Q.1.code]
    refine ⟨fun a b => star (amp a) * amp b * scalar a b, ?_⟩
    intro a b x hx y hy
    by_cases ha : amp a = 0
    · simp [ha]
    by_cases hb : amp b = 0
    · simp [hb]
    calc
      inner Complex
          ((binaryPauliKrausFamily E amp).operator a x)
          ((binaryPauliKrausFamily E amp).operator b y) =
          (star (amp a) * amp b) *
            inner Complex (toQubitOperator (E a) x) (toQubitOperator (E b) y) := by
              rw [binaryPauliKrausFamily_operator, binaryPauliKrausFamily_operator]
              simp
              ring
      _ = (star (amp a) * amp b) *
            inner Complex x
              (toQubitOperator (binaryMul (binaryDagger (E a)) (E b)) y) := by
              rw [inner_toQubitOperator_pair_eq_relative]
      _ = (star (amp a) * amp b) * (scalar a b * inner Complex x y) := by
              rw [hscalar a b ha hb x hx y hy]
      _ = (star (amp a) * amp b * scalar a b) * inner Complex x y := by
              ring
end QEC.Coding.StabilizerCode

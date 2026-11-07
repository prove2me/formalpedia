-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.stabilizerSyndrome_injectiveUpToSign_of_correctable_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:04:21.170831+00:00
-- url     : https://prove2.me/submissions/f6e6c4f5-6a3e-405c-abf8-0f388194366b

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
import Definitions.Def_QEC_Coding_Stabilizer_SyndromeInjectivity
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndrome_map_properties
import Theorems.Thm_QEC_Coding_PauliSymplectic_weight_binaryMul_le
import Theorems.Thm_QEC_Coding_StabilizerCode_exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
import Theorems.Thm_QEC_Coding_StabilizerCode_not_semanticallyDegenerateAtDistance_iff_generated_weight_ge
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
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
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


section
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem inBinaryNormalizer_of_inStabilizerNormalizer_of_generated_eq
    {κ : Type v} [Fintype κ]
    (Q : SourceValidBinary ι) (generators : κ → Binary ι)
    (hgenerated : {S | GeneratedStabilizer generators S} = Q.1.generatedGroup)
    {E : Binary ι} (hE : InStabilizerNormalizer generators E) :
    Q.1.InBinaryNormalizer E := by
  intro S hS
  apply hE S
  have : S ∈ ({P | GeneratedStabilizer generators P} : Set (Binary ι)) := by
    rw [hgenerated]
    exact hS
  exact this
omit [DecidableEq ι] in
private theorem binaryUpToSign_relative_one_iff (E F : Binary ι) :
    BinaryUpToSign (binaryMul (binaryDagger E) F) binaryOne ↔
      BinaryUpToSign E F := by
  have hneg (P : SymplecticVector (ZMod 2) ι) : -P = P := by
    apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
    rw [map_neg]
    change (-P.xPart, -P.zPart) = (P.xPart, P.zPart)
    apply Prod.ext
    · funext i
      exact ZMod.neg_eq_self_mod_two _
    · funext i
      exact ZMod.neg_eq_self_mod_two _
  constructor
  · intro hRelative
    change E.vector + F.vector = 0 at hRelative
    change E.vector = F.vector
    calc
      E.vector = -F.vector := (add_eq_zero_iff_eq_neg.mp hRelative)
      _ = F.vector := hneg F.vector
  · intro hEF
    change E.vector + F.vector = 0
    rw [hEF]
    rw [add_eq_zero_iff_eq_neg]
    exact (hneg F.vector).symm
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
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    {κ : Type v} [Fintype κ] {α : Type w} [Fintype α]
    (Q : SourceValidBinary ι) (generators : κ → Binary ι)
    (hgenerated : {S | GeneratedStabilizer generators S} = Q.1.generatedGroup)
    (d t : Nat) (hd : SemanticStabilizerDistance Q d)
    (hNondegenerate : ¬ SemanticallyDegenerateAtDistance Q d)
    (E : α → Binary ι) (amp : α → Complex)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete)
    (hcorrectable : ∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
        Semantics.FiniteKrausCorrectable α
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι)
          Q.1.code (binaryPauliKrausFamily E amp) recovery)
    (hweight : ∀ i, amp i ≠ 0 → weight (E i) ≤ t)
    (hradius : 2 * t < d) :
    ∀ i j, amp i ≠ 0 → amp j ≠ 0 →
      stabilizerSyndrome generators (E i) = stabilizerSyndrome generators (E j) →
      BinaryUpToSign (E i) (E j) := by
  intro i j hi hj hsyndrome
  let relative := binaryMul (binaryDagger (E i)) (E j)
  have hpairs :=
    (exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
      Q E amp hcomplete).1 hcorrectable
  have hrelativeGenerated : Q.1.InGeneratedGroupUpToSign relative := by
    rcases hpairs i j hi hj with hGenerated | hOutsideNormalizer
    · exact hGenerated
    · have hproperties :=
        stabilizerSyndrome_map_properties generators relative (E i) (E j)
      have hproductZero :
          stabilizerSyndrome generators (binaryMul (E i) (E j)) = 0 :=
        hproperties.2.1.mp hsyndrome
      have hrelativeZero : stabilizerSyndrome generators relative = 0 := by
        calc
          stabilizerSyndrome generators relative =
              stabilizerSyndrome generators (binaryMul (E i) (E j)) :=
            hproperties.2.2.symm
          _ = 0 := hproductZero
      have hgeneratorNormalizer : InStabilizerNormalizer generators relative :=
        hproperties.1.mp hrelativeZero
      have hcodeNormalizer : Q.1.InBinaryNormalizer relative :=
        inBinaryNormalizer_of_inStabilizerNormalizer_of_generated_eq
          Q generators hgenerated hgeneratorNormalizer
      exact False.elim (hOutsideNormalizer hcodeNormalizer)
  have hrelativeWeight : weight relative ≤ weight (E i) + weight (E j) := by
    simpa [relative] using weight_binaryMul_le (binaryDagger (E i)) (E j)
  have hrelativeLt : weight relative < d := by
    have hiWeight := hweight i hi
    have hjWeight := hweight j hj
    omega
  by_cases hidentity : BinaryUpToSign relative binaryOne
  · exact (binaryUpToSign_relative_one_iff (E i) (E j)).1 hidentity
  · have hlower : d ≤ weight relative :=
      (not_semanticallyDegenerateAtDistance_iff_generated_weight_ge Q d hd).1
        hNondegenerate relative hrelativeGenerated hidentity
    omega
end QEC.Coding.StabilizerCode

-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.semanticCode_finrank_eq_two_pow_blockLength_sub_generatorRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:45:04.038879+00:00
-- url     : https://prove2.me/submissions/190cf2e3-f89f-4432-81a7-b64a1bbc9afd

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_card_generatedGroupElement_eq_two_pow_generatorRank
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_nondegenerate
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedVectorSubspace_isotropic
import Theorems.Thm_QEC_Coding_StabilizerCode_toQubitOperator_mul_stabilizerAverage
import Theorems.Thm_QEC_Coding_StabilizerCode_trace_stabilizerAverage
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
open PauliSymplectic
universe u v
namespace StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace BinaryStabilizerPresentation
omit [DecidableEq ι] in
private theorem finrank_symplecticVector :
    Module.finrank (ZMod 2) (SymplecticVector (ZMod 2) ι) =
      2 * Fintype.card ι := by
  rw [(SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).finrank_eq,
    Module.finrank_prod, Module.finrank_pi]
  omega
private theorem generatedVectorSubspace_le_normalizer
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.code.1.generatedVectorSubspace ≤
      FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace :=
  P.code.1.generatedVectorSubspace_isotropic
private theorem finrank_normalizer
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Module.finrank (ZMod 2)
      (FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace) =
      2 * P.blockLength - P.generatorRank := by
  rw [LinearMap.BilinForm.finrank_orthogonal FiniteSymplectic.form_nondegenerate,
    finrank_symplecticVector, blockLength, generatorRank]
private theorem generatorRank_le_blockLength
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.generatorRank ≤ P.blockLength := by
  have hle := Submodule.finrank_mono P.generatedVectorSubspace_le_normalizer
  rw [P.finrank_normalizer] at hle
  change P.generatorRank ≤ 2 * P.blockLength - P.generatorRank at hle
  omega
private theorem semanticCodeProjector_isProj
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    LinearMap.IsProj P.semanticCode.carrier P.semanticCodeProjector := by
  constructor
  · intro ψ
    apply (P.code.2.2 _).2
    intro G hG
    let S : P.code.1.GeneratedGroupElement := ⟨G, hG⟩
    change toQubitOperator G
      ((Fintype.card P.code.1.GeneratedGroupElement : Complex)⁻¹ •
        P.code.1.stabilizerAverage ψ) =
      (Fintype.card P.code.1.GeneratedGroupElement : Complex)⁻¹ •
        P.code.1.stabilizerAverage ψ
    rw [map_smul]
    congr 1
    have haverage := congrArg
      (fun A : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => A ψ)
      (StabilizerCode.toQubitOperator_mul_stabilizerAverage P.code.1 S)
    simpa [S, Module.End.mul_apply] using haverage
  · intro ψ hψ
    have hcard : (Fintype.card P.code.1.GeneratedGroupElement : Complex) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    change (Fintype.card P.code.1.GeneratedGroupElement : Complex)⁻¹ •
      P.code.1.stabilizerAverage ψ = ψ
    have hfixed : ∀ G : P.code.1.GeneratedGroupElement,
        toQubitOperator G.1 ψ = ψ := fun G => (P.code.2.2 ψ).1 hψ G.1 G.2
    rw [StabilizerCode.stabilizerAverage, LinearMap.sum_apply]
    simp_rw [hfixed]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul Complex,
      smul_smul, inv_mul_cancel₀ hcard, one_smul]
private theorem trace_semanticCodeProjector
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) P.semanticCodeProjector =
      (2 ^ (P.blockLength - P.generatorRank) : Nat) := by
  rw [semanticCodeProjector, map_smul, StabilizerCode.trace_stabilizerAverage P.code,
    P.card_generatedGroupElement_eq_two_pow_generatorRank, blockLength]
  have hle := P.generatorRank_le_blockLength
  change P.generatorRank ≤ Fintype.card ι at hle
  have hpow := Nat.pow_sub_mul_pow 2 hle
  rw [← hpow, Nat.cast_mul]
  have hnonzero : ((2 ^ P.generatorRank : Nat) : Complex) ≠ 0 := by
    exact_mod_cast pow_ne_zero P.generatorRank (by omega : 2 ≠ 0)
  rw [smul_eq_mul]
  calc
    (↑((2 : Nat) ^ P.generatorRank) : Complex)⁻¹ *
        (↑((2 : Nat) ^ (Fintype.card ι - P.generatorRank)) *
          ↑((2 : Nat) ^ P.generatorRank)) =
        ((↑((2 : Nat) ^ P.generatorRank) : Complex)⁻¹ *
          ↑((2 : Nat) ^ P.generatorRank)) *
          ↑((2 : Nat) ^ (Fintype.card ι - P.generatorRank)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hnonzero, one_mul]
end BinaryStabilizerPresentation
namespace StabilizerParameterData
end StabilizerParameterData
end StabilizerCode
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Module.finrank Complex P.semanticCode.carrier =
      2 ^ (P.blockLength - P.generatorRank) := by
  have hfinrank :
      (Module.finrank Complex P.semanticCode.carrier : Complex) =
        (2 ^ (P.blockLength - P.generatorRank) : Nat) :=
    (P.semanticCodeProjector_isProj.trace).symm.trans P.trace_semanticCodeProjector
  exact_mod_cast hfinrank
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

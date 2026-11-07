-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.kernel_word_has_no_left_unique_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:40:19.015921+00:00
-- url     : https://prove2.me/submissions/5f459ce4-8c77-4d8c-b427-7b75d8a59e39

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_mem_leftNeighborhood_iff_inducedDegree_pos
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_firstCode_transposeData
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_fst_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_snd_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_secondTransposeCode_transposeData
import Theorems.Thm_QEC_Coding_HypergraphProduct_supportExtendedWitness_apply_mem
import Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_inl_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_inr_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_swapWord
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordTensorEquiv_tmul_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_zeroExtend_apply_mem
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
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
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.firstCode_transposeData
attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_fst_apply
attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_snd_apply
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.secondTransposeCode_transposeData
attribute [local simp] QEC.Coding.HypergraphProduct.supportExtendedWitness_apply_mem
attribute [local simp] QEC.Coding.HypergraphProduct.swapWord_inl_apply
attribute [local simp] QEC.Coding.HypergraphProduct.swapWord_inr_apply
attribute [local simp] QEC.Coding.HypergraphProduct.swapWord_swapWord
attribute [local simp] QEC.Coding.HypergraphProduct.wordTensorEquiv_tmul_apply
attribute [local simp] QEC.Coding.HypergraphProduct.zeroExtend_apply_mem
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
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


attribute [local simp] QEC.Coding.QuantumExpander.BiregularBipartiteGraph.mem_leftNeighborhood_iff_inducedDegree_pos

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
open QEC.Coding.QuantumExpander.BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
namespace QEC.Coding.QuantumExpander.BiregularBipartiteGraph
theorem _root_.solution
    (G : BiregularBipartiteGraph A B) (x : Word (ZMod 2) A)
    (hxKernel : Matrix.toLin' G.incidenceMatrix x = 0) (b : B) :
    G.leftInducedDegree (hammingSupport x) b ≠ 1 := by
  intro hUnique
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hUnique
  have haFiltered : a ∈
      (hammingSupport x).filter (fun a => G.adjacent a b = true) := by
    rw [ha]
    simp
  have haSupport : a ∈ hammingSupport x := (Finset.mem_filter.mp haFiltered).1
  have haAdjacent : G.adjacent a b = true := (Finset.mem_filter.mp haFiltered).2
  have hxa : x a ≠ 0 := (Finset.mem_filter.mp haSupport).2
  have hsum :
      ∑ a', G.incidenceMatrix b a' * x a' = x a := by
    rw [Finset.sum_eq_single a]
    · simp [incidenceMatrix, haAdjacent]
    · intro a' _ha' hne
      by_cases hadj : G.adjacent a' b = true
      · have hxa' : x a' = 0 := by
          by_contra hxa'0
          have ha'Mem : a' ∈
              (hammingSupport x).filter (fun c => G.adjacent c b = true) := by
            simp [hammingSupport, hxa'0, hadj]
          rw [ha] at ha'Mem
          exact hne (Finset.mem_singleton.mp ha'Mem)
        simp [incidenceMatrix, hadj, hxa']
      · simp [incidenceMatrix, hadj]
    · simp
  have hb := congrFun hxKernel b
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] at hb
  rw [hsum] at hb
  exact hxa hb
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph

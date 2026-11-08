-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.leverrierTillichZemorQuantumExpanderParameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:47:03.712194+00:00
-- url     : https://prove2.me/submissions/dd1eb451-dab2-4f14-bd72-507cad667d05

import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Definitions.Def_QEC_Results_QLDPC_QuantumExpanderParameters
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_stabilizer_isSourceValidBinary
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
import Theorems.Thm_QEC_Coding_HypergraphProduct_xCheckWeight_diagonal_eq
import Theorems.Thm_QEC_Coding_HypergraphProduct_zCheckWeight_diagonal_eq
import Theorems.Thm_QEC_Coding_HypergraphProduct_zeroExtend_apply_mem
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_card_qubitIndex_hypergraphProductData
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_columnWeight_incidenceMatrix
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_finrank_middleHomology_ge_card_sub_sq
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_leftDegree_le_rightDegree
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_mem_leftNeighborhood_iff_inducedDegree_pos
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_quantumDistance_eq_min_classicalDistances
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_quantumDistance_expansion_bound
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_rowWeight_incidenceMatrix
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
attribute [local simp] QEC.Coding.QuantumExpander.BiregularBipartiteGraph.mem_leftNeighborhood_iff_inducedDegree_pos
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
    (G : QEC.Coding.QuantumExpander.BiregularBipartiteGraph A B)
    (hSize : Fintype.card B ≤ Fintype.card A)
    {γA δA γB δB : Real}
    (hγA : 0 < γA) (hδApos : 0 < δA)
    (hγB : 0 < γB) (hδBpos : 0 < δB)
    (hExpand : G.LeftRightExpanding γA δA γB δB)
    (hδA : δA < 1 / 2) (hδB : δB < 1 / 2) :
    G.leftDegree ≤ G.rightDegree ∧
    (binaryCSSCode G.hypergraphProductData).stabilizer.IsSourceValidBinary ∧
    Fintype.card (QubitIndex B A B A) =
      Fintype.card A ^ 2 + Fintype.card B ^ 2 ∧
    (Fintype.card A - Fintype.card B) ^ 2 ≤
      Module.finrank (ZMod 2)
        (chainComplex G.hypergraphProductData).middleHomology ∧
    (∀ b a, HammingWeight
        (wordLinearMapTranspose (boundary1 G.hypergraphProductData)
          (Pi.single (b, a) 1)) = G.leftDegree + G.rightDegree) ∧
    (∀ a b, HammingWeight
        (boundary2 G.hypergraphProductData (Pi.single (a, b) 1)) =
          G.leftDegree + G.rightDegree) ∧
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode G.hypergraphProductData).xCode
        (binaryCSSCode G.hypergraphProductData).zCode =
      min
        (extendedMinimumDistance (firstCode G.hypergraphProductData))
        (extendedMinimumDistance
          (firstTransposeCode G.hypergraphProductData)) ∧
    ENNReal.ofReal
        (min (γA * Fintype.card A) (γB * Fintype.card B)) ≤
      extendedNatToENNReal
        (extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode G.hypergraphProductData).xCode
          (binaryCSSCode G.hypergraphProductData).zCode) := by
  have _hSourcePositiveParameters :
      0 < γA ∧ 0 < δA ∧ 0 < γB ∧ 0 < δB :=
    ⟨hγA, hδApos, hγB, hδBpos⟩
  refine ⟨leftDegree_le_rightDegree G hSize,
    binaryCSSCode_stabilizer_isSourceValidBinary G.hypergraphProductData,
    card_qubitIndex_hypergraphProductData G,
    finrank_middleHomology_ge_card_sub_sq G hSize, ?_, ?_,
    quantumDistance_eq_min_classicalDistances G,
    quantumDistance_expansion_bound G hExpand hδA hδB⟩
  · intro b a
    calc
      HammingWeight
          (wordLinearMapTranspose (boundary1 G.hypergraphProductData)
            (Pi.single (b, a) 1)) =
          rowWeight G.incidenceMatrix b +
            columnWeight G.incidenceMatrix a := by
        simpa [hypergraphProductData] using
          (xCheckWeight_diagonal_eq G.incidenceMatrix b a)
      _ = G.leftDegree + G.rightDegree := by
        rw [rowWeight_incidenceMatrix, columnWeight_incidenceMatrix, add_comm]
  · intro a b
    calc
      HammingWeight
          (boundary2 G.hypergraphProductData (Pi.single (a, b) 1)) =
          rowWeight G.incidenceMatrix b +
            columnWeight G.incidenceMatrix a := by
        simpa [hypergraphProductData] using
          (zCheckWeight_diagonal_eq G.incidenceMatrix a b)
      _ = G.leftDegree + G.rightDegree := by
        rw [rowWeight_incidenceMatrix, columnWeight_incidenceMatrix, add_comm]
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph

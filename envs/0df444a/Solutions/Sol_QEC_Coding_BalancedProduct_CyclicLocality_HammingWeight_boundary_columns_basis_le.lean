-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_boundary_columns_basis_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:25:44.261177+00:00
-- url     : https://prove2.me/submissions/3546ea00-8858-4025-a37e-fd46301230ab

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicLocality_HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicLocality_HammingWeight_leftRegular_cyclicBoundaryElement_col_le_two
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicEquiv_apply_eq_generator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicInvEquiv_apply_eq_invGenerator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_B_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_B
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_dualData
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inl_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inr_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_swapWord
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_precomp_equiv
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_horizontalPart_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_boundary1_canonicalBasisWord_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_transpose_boundary2_canonicalBasisWord_apply
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
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicEquiv_apply_eq_generator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_A
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_B_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_A
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_B
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_dualData
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inl_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inr_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_swapWord
attribute [local simp] QEC.Coding.BalancedProduct.PKDistance.horizontalPart_apply
attribute [local simp] QEC.Coding.BalancedProduct.PKDistance.verticalPart_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
attribute [local simp] QEC.Coding.FiberBundle.homologyBaseProjection_add
attribute [local simp] QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inl
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inr
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
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


section
noncomputable section
namespace QEC.Coding.BalancedProduct.CyclicLocality
open QEC.Coding
open PKDistance
universe u v
private theorem HammingWeight_dropUnit
    {F I G : Type*} [Zero F] [DecidableEq F]
    [Fintype I] [Fintype G] (z : Word F (I × G)) :
    HammingWeight (fun p : I × Unit × G => z (p.1, p.2.2)) =
      HammingWeight z := by
  exact HammingWeight_precomp_equiv (dropUnitEquiv I G) z
private theorem HammingWeight_fixed_first
    {F B I : Type*} [Zero F] [DecidableEq F]
    [Fintype B] [DecidableEq B] [Fintype I]
    (b : B) (y : Word F I) :
    HammingWeight (fun p : B × I => if b = p.1 then y p.2 else 0) =
      HammingWeight y := by
  classical
  let sourceWord : Word F (B × I) :=
    fun p => if b = p.1 then y p.2 else 0
  let e : {p : B × I // sourceWord p ≠ 0} ≃ {i : I // y i ≠ 0} :=
    { toFun := fun p =>
        ⟨p.1.2, by
          by_contra hy
          exact p.2 (by simp [sourceWord, hy])⟩
      invFun := fun i =>
        ⟨(b, i.1), by
          dsimp [sourceWord]
          simpa using i.2⟩
      left_inv := by
        rintro ⟨⟨b', i⟩, hp⟩
        apply Subtype.ext
        change (b, i) = (b', i)
        apply Prod.ext
        · dsimp [sourceWord] at hp
          by_cases hbb : b = b'
          · exact hbb
          · simp [hbb] at hp
        · rfl
      right_inv := by
        rintro ⟨i, hi⟩
        rfl }
  calc
    HammingWeight sourceWord =
        Fintype.card {p : B × I // sourceWord p ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {i : I // y i ≠ 0} := Fintype.card_congr e
    _ = HammingWeight y := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
private theorem tannerAction_single_apply
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (c : aCol) (gi : G) (r : aRow) (go : G) :
    tannerAction A (Pi.single (c, gi) 1) (r, go) =
      LiftedProduct.rightRegularMatrix (A r c) go gi := by
  rw [tannerAction_apply, Fintype.sum_eq_single c]
  · rw [Fintype.sum_eq_single gi]
    · simp
    · intro g hne
      simp [hne]
  · intro c' hne
    simp [hne]
end QEC.Coding.BalancedProduct.CyclicLocality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicLocality
open QEC.Coding
open PKDistance
universe u v
namespace QEC.Coding.BalancedProduct.CyclicLocality
theorem _root_.solution
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    {forwardBound transposeBound : Nat}
    (hForward : ∀ i : aCol × G,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ forwardBound)
    (hTranspose : ∀ i : aRow × G,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤
          transposeBound)
    (q : LiftedProduct.QubitIndex aRow aCol Unit Unit G) :
    HammingWeight
        (LiftedProduct.boundary1 (Cyclic.liftedProductData A x)
          (canonicalBasisWord (F := ZMod 2) q)) +
      HammingWeight
        (wordLinearMapTranspose
          (LiftedProduct.boundary2 (Cyclic.liftedProductData A x))
          (canonicalBasisWord (F := ZMod 2) q)) ≤
      max forwardBound transposeBound + 2 := by
  let D := Cyclic.liftedProductData A x
  cases q with
  | inl p =>
      rcases p with ⟨c, ⟨u, gi⟩⟩
      cases u
      have hBoundary1 :
          HammingWeight
              (LiftedProduct.boundary1 D
                (canonicalBasisWord (F := ZMod 2) (Sum.inl (c, (), gi)))) =
            HammingWeight (tannerAction A (Pi.single (c, gi) 1)) := by
        rw [show LiftedProduct.boundary1 D
            (canonicalBasisWord (F := ZMod 2) (Sum.inl (c, (), gi))) =
            fun p : aRow × Unit × G =>
              tannerAction A (Pi.single (c, gi) 1) (p.1, p.2.2) by
          funext p
          rcases p with ⟨r, ⟨u, go⟩⟩
          cases u
          rw [LiftedProduct.boundary1_canonicalBasisWord_apply]
          rw [tannerAction_single_apply]
          rfl]
        exact HammingWeight_dropUnit _
      have hBoundary2 :
          HammingWeight
              (wordLinearMapTranspose (LiftedProduct.boundary2 D)
                (canonicalBasisWord (F := ZMod 2) (Sum.inl (c, (), gi)))) =
            HammingWeight (fun go =>
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) gi go) := by
        rw [show HammingWeight
            (wordLinearMapTranspose (LiftedProduct.boundary2 D)
              (canonicalBasisWord (F := ZMod 2) (Sum.inl (c, (), gi)))) =
            HammingWeight (fun p : aCol × Unit × G =>
              if c = p.1 then
                LiftedProduct.leftRegularMatrix
                  (Cyclic.cyclicBoundaryElement x) gi p.2.2 else 0) by
          apply congrArg HammingWeight
          funext p
          rcases p with ⟨c', ⟨u, go⟩⟩
          cases u
          rw [LiftedProduct.transpose_boundary2_canonicalBasisWord_apply]
          simp [D, LiftedProduct.boundary2Matrix_inl_apply]]
        rw [show HammingWeight
            (fun p : aCol × Unit × G => if c = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) gi p.2.2 else 0) =
            HammingWeight (fun p : aCol × G => if c = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) gi p.2 else 0) by
          simpa using (HammingWeight_dropUnit
            (z := fun p : aCol × G => if c = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) gi p.2 else 0))]
        exact HammingWeight_fixed_first c
          (fun go : G => LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) gi go)
      rw [hBoundary1, hBoundary2]
      exact Nat.add_le_add
        ((hForward (c, gi)).trans (Nat.le_max_left _ _))
        (HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two x gi)
  | inr p =>
      rcases p with ⟨r, ⟨u, gi⟩⟩
      cases u
      have hBoundary1 :
          HammingWeight
              (LiftedProduct.boundary1 D
                (canonicalBasisWord (F := ZMod 2) (Sum.inr (r, (), gi)))) =
            HammingWeight (fun go =>
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) go gi) := by
        rw [show HammingWeight
            (LiftedProduct.boundary1 D
              (canonicalBasisWord (F := ZMod 2) (Sum.inr (r, (), gi)))) =
            HammingWeight (fun p : aRow × Unit × G =>
              if r = p.1 then
                LiftedProduct.leftRegularMatrix
                  (Cyclic.cyclicBoundaryElement x) p.2.2 gi else 0) by
          apply congrArg HammingWeight
          funext p
          rcases p with ⟨r', ⟨u, go⟩⟩
          cases u
          rw [LiftedProduct.boundary1_canonicalBasisWord_apply]
          by_cases h : r' = r
          · simp [D, h]
          · simp [D, h, Ne.symm h]]
        rw [show HammingWeight
            (fun p : aRow × Unit × G => if r = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) p.2.2 gi else 0) =
            HammingWeight (fun p : aRow × G => if r = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) p.2 gi else 0) by
          simpa using (HammingWeight_dropUnit
            (z := fun p : aRow × G => if r = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) p.2 gi else 0))]
        exact HammingWeight_fixed_first r
          (fun go : G => LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) go gi)
      have hBoundary2 :
          HammingWeight
              (wordLinearMapTranspose (LiftedProduct.boundary2 D)
                (canonicalBasisWord (F := ZMod 2) (Sum.inr (r, (), gi)))) =
            HammingWeight
              (tannerAction (LiftedProduct.starTranspose A)
                (Pi.single (r, gi) 1)) := by
        rw [show wordLinearMapTranspose (LiftedProduct.boundary2 D)
            (canonicalBasisWord (F := ZMod 2) (Sum.inr (r, (), gi))) =
            fun p : aCol × Unit × G =>
              tannerAction (LiftedProduct.starTranspose A)
                (Pi.single (r, gi) 1) (p.1, p.2.2) by
          funext p
          rcases p with ⟨c, ⟨u, go⟩⟩
          cases u
          rw [LiftedProduct.transpose_boundary2_canonicalBasisWord_apply]
          rw [tannerAction_single_apply]
          simp [D, Cyclic.liftedProductData,
            LiftedProduct.boundary2Matrix_inr_apply,
            LiftedProduct.starTranspose_apply,
            LiftedProduct.rightRegularMatrix]]
        exact HammingWeight_dropUnit _
      rw [hBoundary1, hBoundary2]
      calc
        HammingWeight (fun go => LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) go gi) +
            HammingWeight
              (tannerAction (LiftedProduct.starTranspose A)
                (Pi.single (r, gi) 1)) ≤
          2 + max forwardBound transposeBound := Nat.add_le_add
            (HammingWeight_leftRegular_cyclicBoundaryElement_col_le_two x gi)
            ((hTranspose (r, gi)).trans (Nat.le_max_right _ _))
        _ = max forwardBound transposeBound + 2 := Nat.add_comm _ _
end QEC.Coding.BalancedProduct.CyclicLocality

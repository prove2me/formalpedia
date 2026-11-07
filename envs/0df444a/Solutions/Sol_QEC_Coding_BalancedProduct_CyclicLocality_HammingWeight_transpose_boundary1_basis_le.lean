-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_transpose_boundary1_basis_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:24:13.451941+00:00
-- url     : https://prove2.me/submissions/7f5f8df6-7db4-4926-bcd5-6bff949adf35

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicLocality_HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two
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
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
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
private theorem HammingWeight_sum_elim
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [Fintype B] (x : Word F A) (y : Word F B) :
    HammingWeight (Sum.elim x y) = HammingWeight x + HammingWeight y := by
  classical
  let e :
      {s : Sum A B // Sum.elim x y s ≠ 0} ≃
        Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0} :=
    { toFun := fun s =>
        match s with
        | ⟨Sum.inl a, ha⟩ => Sum.inl ⟨a, ha⟩
        | ⟨Sum.inr b, hb⟩ => Sum.inr ⟨b, hb⟩
      invFun := fun s =>
        match s with
        | Sum.inl a => ⟨Sum.inl a.1, a.2⟩
        | Sum.inr b => ⟨Sum.inr b.1, b.2⟩
      left_inv := by rintro ⟨a | b, ha⟩ <;> rfl
      right_inv := by rintro (a | b) <;> rfl }
  calc
    HammingWeight (Sum.elim x y) =
        Fintype.card {s : Sum A B // Sum.elim x y s ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card
        (Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0}) :=
      Fintype.card_congr e
    _ = HammingWeight x + HammingWeight y := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
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
    {tannerBound : Nat}
    (hTanner : ∀ i : aRow × G,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤
          tannerBound)
    (c0 : LiftedProduct.C0Index aRow Unit G) :
    HammingWeight
        (wordLinearMapTranspose
          (LiftedProduct.boundary1 (Cyclic.liftedProductData A x))
          (canonicalBasisWord (F := ZMod 2) c0)) ≤
      tannerBound + 2 := by
  rcases c0 with ⟨r, ⟨u, go⟩⟩
  cases u
  let D := Cyclic.liftedProductData A x
  let left : Word (ZMod 2) (aCol × Unit × G) := fun p =>
    tannerAction (LiftedProduct.starTranspose A) (Pi.single (r, go) 1)
      (p.1, p.2.2)
  let right : Word (ZMod 2) (aRow × Unit × G) := fun p =>
    if r = p.1 then
      LiftedProduct.leftRegularMatrix
        (Cyclic.cyclicBoundaryElement x) go p.2.2
    else 0
  have hword :
      wordLinearMapTranspose (LiftedProduct.boundary1 D)
          (canonicalBasisWord (F := ZMod 2) (r, (), go)) =
        Sum.elim left right := by
    funext q
    rw [LiftedProduct.transpose_boundary1_canonicalBasisWord_apply]
    cases q with
    | inl p =>
        rcases p with ⟨c, ⟨u, gi⟩⟩
        cases u
        simp [left, tannerAction_apply, D,
          LiftedProduct.boundary1Matrix_inl_apply,
          LiftedProduct.starTranspose_apply,
          LiftedProduct.rightRegularMatrix, Pi.single_apply]
        rw [Fintype.sum_eq_single r]
        · rw [Fintype.sum_eq_single go]
          · simp
          · intro g hne
            simp [hne]
        · intro r' hne
          simp [hne]
    | inr p =>
        rcases p with ⟨r', ⟨u, gi⟩⟩
        cases u
        simp [right, D]
  rw [hword, HammingWeight_sum_elim]
  have hLeft : HammingWeight left =
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single (r, go) 1)) :=
    HammingWeight_dropUnit _
  have hRight : HammingWeight right = HammingWeight (fun gi =>
      LiftedProduct.leftRegularMatrix (Cyclic.cyclicBoundaryElement x) go gi) := by
    rw [show HammingWeight right = HammingWeight
        (fun p : aRow × G => if r = p.1 then
          LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) go p.2 else 0) by
      simpa [right] using (HammingWeight_dropUnit
        (z := fun p : aRow × G => if r = p.1 then
          LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) go p.2 else 0))]
    exact HammingWeight_fixed_first r _
  rw [hLeft, hRight]
  exact Nat.add_le_add (hTanner (r, go))
    (HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two x go)
end QEC.Coding.BalancedProduct.CyclicLocality

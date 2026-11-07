-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.middleCohomologyDistanceAtMost_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:22:09.132208+00:00
-- url     : https://prove2.me/submissions/41a6c334-844b-4723-90a2-30f618b1b340

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
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
namespace QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
private theorem exists_standardBasis_not_coboundary
    {G aRow aCol : Type}
    [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (hCard : Fintype.card aRow < Fintype.card aCol) :
    ∃ c : aCol, (Pi.single c 1 : Word (ZMod 2) aCol) ∉
      (HorizontalSubsystem.quotientTannerComplex A).firstCoboundaryCheckCode.carrier := by
  by_contra h
  push_neg at h
  have hTop :
      (HorizontalSubsystem.quotientTannerComplex A).firstCoboundaryCheckCode.carrier =
        ⊤ := by
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun (ZMod 2) aCol)).2
    intro c
    simpa using h c
  have hRangeLe : Module.finrank (ZMod 2)
      (HorizontalSubsystem.quotientTannerComplex A).firstCoboundaryCheckCode.carrier ≤
      Fintype.card aRow := by
    change Module.finrank (ZMod 2)
        (LinearMap.range
          (wordLinearMapTranspose (HorizontalSubsystem.quotientBoundary A))) ≤ _
    calc
      Module.finrank (ZMod 2)
          (LinearMap.range
            (wordLinearMapTranspose (HorizontalSubsystem.quotientBoundary A))) ≤
          Module.finrank (ZMod 2) (Word (ZMod 2) aRow) :=
        LinearMap.finrank_range_le _
      _ = Fintype.card aRow := by simp
  rw [hTop] at hRangeLe
  simp at hRangeLe
  omega
private theorem wordLinearMapTranspose_apply_eq_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κ)
    (y : Word (ZMod 2) κ) (i : ι) :
    wordLinearMapTranspose P y i =
      ∑ k : κ, y k * P (canonicalBasisWord i) k := by
  classical
  rw [wordLinearMapTranspose]
  rfl
private theorem HammingWeight_transpose_horizontalAugmentation_single
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (c : aCol) :
    HammingWeight
        (wordLinearMapTranspose
          (HorizontalSubsystem.horizontalAugmentation
            (aRow := aRow) (aCol := aCol) (G := G))
          (Pi.single c 1)) =
      Fintype.card G := by
  classical
  have hTranspose :
      wordLinearMapTranspose
          (HorizontalSubsystem.horizontalAugmentation
            (aRow := aRow) (aCol := aCol) (G := G)) =
        HorizontalSubsystem.horizontalConstant := by
    apply LinearMap.ext
    intro z
    funext q
    cases q with
    | inl p =>
        rcases p with ⟨c', u, g⟩
        cases u
        rw [wordLinearMapTranspose_apply_eq_sum]
        rw [HorizontalSubsystem.horizontalConstant_inl]
        simp_rw [HorizontalSubsystem.horizontalAugmentation_apply]
        unfold canonicalBasisWord
        rw [Finset.sum_eq_single c']
        · rw [Finset.sum_eq_single g]
          · simp
          · intro b _ hb
            simp [Pi.single_apply, hb]
          · simp
        · intro k _ hk
          simp [Pi.single_apply, hk]
        · simp
    | inr p =>
        rcases p with ⟨r, u, g⟩
        cases u
        rw [wordLinearMapTranspose_apply_eq_sum]
        rw [HorizontalSubsystem.horizontalConstant_inr]
        simp_rw [HorizontalSubsystem.horizontalAugmentation_apply]
        unfold canonicalBasisWord
        simp [Pi.single_apply]
  rw [hTranspose]
  rw [HammingWeight_eq_card_hammingSupport]
  let supportFinset :
      Finset (LiftedProduct.QubitIndex aRow aCol Unit Unit G) :=
    Finset.univ.filter (fun q =>
      ∃ u : Unit, ∃ g : G, q = Sum.inl (c, u, g))
  have hSupport : hammingSupport
      (HorizontalSubsystem.horizontalConstant
        (aRow := aRow) (aCol := aCol) (G := G)
        (Pi.single c 1)) =
      supportFinset := by
    ext q
    simp only [hammingSupport, supportFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    cases q with
    | inl p =>
        rcases p with ⟨c', u, g⟩
        cases u
        by_cases hcc : c' = c
        · subst c'
          rw [HorizontalSubsystem.horizontalConstant_inl]
          simp
        · rw [HorizontalSubsystem.horizontalConstant_inl]
          simp [hcc]
    | inr p =>
        rcases p with ⟨r, u, g⟩
        cases u
        rw [HorizontalSubsystem.horizontalConstant_inr]
        simp
  rw [hSupport]
  let f : G → supportFinset := fun g =>
      ⟨(Sum.inl (c, (), g) :
        LiftedProduct.QubitIndex aRow aCol Unit Unit G), by
          dsimp [supportFinset]
          simp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g h hEq
      simpa [f] using congrArg
        (fun q : supportFinset => match q.1 with
          | Sum.inl p => p.2.2
          | Sum.inr p => p.2.2) hEq
    · rintro ⟨q, hq⟩
      dsimp [supportFinset] at hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rcases hq with ⟨u, g, rfl⟩
      cases u
      exact ⟨g, by simp [f, supportFinset]⟩
  let e : G ≃ supportFinset := Equiv.ofBijective f hf
  calc
    supportFinset.card = Fintype.card supportFinset :=
      (Fintype.card_coe supportFinset).symm
    _ = Fintype.card G := (Fintype.card_congr e).symm
end QEC.Coding.ExpanderCodes.PK20
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (x : G) (hOdd : Odd (Fintype.card G))
    (hCard : Fintype.card aRow < Fintype.card aCol) :
    MiddleCohomologyDistanceAtMost
      (LiftedProduct.chainComplex (Cyclic.liftedProductData A x))
      (Fintype.card G) := by
  obtain ⟨c, hc⟩ := exists_standardBasis_not_coboundary A hCard
  let e : Word (ZMod 2) aCol := Pi.single c 1
  have heCocycle : e ∈
      (HorizontalSubsystem.quotientTannerComplex A).middleCocycleCode.carrier := by
    rw [(HorizontalSubsystem.quotientTannerComplex A).mem_middleCocycleCode_iff]
    simp [HorizontalSubsystem.quotientTannerComplex,
      wordLinearMapTranspose_zero]
  let eCocycle :
      (HorizontalSubsystem.quotientTannerComplex A).middleCocycleCode.carrier :=
    ⟨e, heCocycle⟩
  let f := HorizontalSubsystem.augmentationChainMap A x
  let s := HorizontalSubsystem.constantChainMap A x
  let z := wordLinearMapTranspose f.map1 e
  have hzCocycle : z ∈
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).middleCocycleCode.carrier :=
    (f.mapMiddleCocycle eCocycle).2
  have heClassNe :
      (HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ
        eCocycle ≠ 0 := by
    intro hzero
    apply hc
    change eCocycle ∈
      (HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles
    exact (Submodule.Quotient.mk_eq_zero _).1 hzero
  have hzNotCoboundary : z ∉
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).firstCoboundaryCheckCode.carrier := by
    intro hzBoundary
    have hzClassZero :
        (LiftedProduct.chainComplex
          (Cyclic.liftedProductData A x)).middleCoboundaryInCocycles.mkQ
            (f.mapMiddleCocycle eCocycle) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hzBoundary
    apply heClassNe
    have hComposition := ThreeTermChainMap.inducedMiddleCohomology_comp f s
    have hSplit : (f.comp s).inducedMiddleCohomology = LinearMap.id := by
      apply LinearMap.ext
      intro y
      change (f.comp s).inducedMiddleCohomology y = y
      obtain ⟨representative, rfl⟩ :=
        (HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ_surjective y
      rw [ThreeTermChainMap.inducedMiddleCohomology_mk]
      congr 1
      apply Subtype.ext
      change wordLinearMapTranspose ((f.comp s).map1) representative.1 =
        representative.1
      rw [ThreeTermChainMap.comp_map1]
      have hMap1 : f.map1.comp s.map1 =
          (LinearMap.id : Word (ZMod 2) aCol →ₗ[ZMod 2]
            Word (ZMod 2) aCol) := by
        dsimp [f, s, HorizontalSubsystem.augmentationChainMap,
          HorizontalSubsystem.constantChainMap]
        exact HorizontalSubsystem.horizontalAugmentation_comp_horizontalConstant_of_odd
          (aRow := aRow) hOdd
      rw [hMap1, wordLinearMapTranspose_id]
      rfl
    calc
      (HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ
          eCocycle =
          (f.comp s).inducedMiddleCohomology
            ((HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ
              eCocycle) := by rw [hSplit]; rfl
      _ = s.inducedMiddleCohomology
          (f.inducedMiddleCohomology
            ((HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ
              eCocycle)) := by rw [hComposition]; rfl
      _ = 0 := by rw [ThreeTermChainMap.inducedMiddleCohomology_mk, hzClassZero, map_zero]
  refine ⟨z, hzCocycle, hzNotCoboundary, ?_⟩
  change HammingWeight
      (wordLinearMapTranspose
        (HorizontalSubsystem.horizontalAugmentation
          (aRow := aRow) (aCol := aCol) (G := G)) e) ≤ _
  rw [show e = Pi.single c 1 by rfl,
    HammingWeight_transpose_horizontalAugmentation_single]
end QEC.Coding.ExpanderCodes.PK20

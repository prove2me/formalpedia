-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agEvaluation_distance_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:34:14.851882+00:00
-- url     : https://prove2.me/submissions/8774d65e-80eb-4090-b05b-5fc3d415f7fc

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_eq_bot_of_negative_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZeroOn_mem_riemannRochSubmodule_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_degree_eq_card
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_extendedMinimumDistance_eq_top_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_le_finitePredicateMinimum
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
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


attribute [local simp] QEC.Coding.AlgebraicGeometry.agWordStar_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [Fintype k] [DecidableEq k] [DecidableEq ι]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (Int.toNat ((Fintype.card ι : ℤ) -
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) : WithTop Nat) ≤
      QEC.Coding.HypergraphProduct.extendedMinimumDistance (agEvaluationCode G Q hG) := by
  classical
  by_cases hdegree : 0 ≤ Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G
  · rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
    apply QEC.Coding.HypergraphProduct.le_finitePredicateMinimum
    intro x hx
    change x ∈ (agEvaluationLinearMap G Q hG).range ∧ x ≠ 0 at hx
    rcases hx with ⟨hxrange, hxzero⟩
    rcases hxrange with ⟨f, rfl⟩
    let S : Finset ι := Finset.univ.filter fun i => agEvaluationLinearMap G Q hG f i = 0
    have hzeroOn : ∀ i, i ∈ S → agEvaluationLinearMap G Q hG f i = 0 := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hmem : (f : F) ∈
        GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S) :=
      evaluationZeroOn_mem_riemannRochSubmodule_sub G Q hQ hG S f hzeroOn
    have hnotNegative : ¬ Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (G - zeroCoordinateDivisor Q S) < 0 := by
      intro hnegative
      have hbot := GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
        k F (G - zeroCoordinateDivisor Q S) hnegative
      have hfzero : (f : F) = 0 := by
        have hmemBot : (f : F) ∈ (⊥ : Submodule k F) := by
          rw [← hbot]
          exact hmem
        exact (Submodule.mem_bot k).mp hmemBot
      apply hxzero
      have hfsubtype : f = 0 := by
        apply Subtype.ext
        exact hfzero
      simpa [hfsubtype]
    have hzeroCardLe : (S.card : ℤ) ≤
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G := by
      by_contra hnot
      apply hnotNegative
      rw [Divisor.degree_sub, zeroCoordinateDivisor_degree_eq_card]
      omega
    have hzeroCardLeNat : S.card ≤ Int.toNat
        (Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) := by
      omega
    have hnonzeroSupport :
        (Finset.univ.filter fun i : ι => ¬ agEvaluationLinearMap G Q hG f i = 0) =
          hammingSupport (agEvaluationLinearMap G Q hG f) := by
      ext i
      simp [hammingSupport]
    have hzeroCard : S.card =
        Fintype.card ι - HammingWeight (agEvaluationLinearMap G Q hG f) := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun i : ι => agEvaluationLinearMap G Q hG f i = 0)
      rw [hnonzeroSupport, ← HammingWeight_eq_card_hammingSupport] at hpartition
      have hunivCard : (Finset.univ : Finset ι).card = Fintype.card ι := by
        simp
      rw [hunivCard] at hpartition
      exact Nat.eq_sub_of_add_eq hpartition
    have hweight : Fintype.card ι - Int.toNat
        (Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) ≤
          HammingWeight (agEvaluationLinearMap G Q hG f) := by
      omega
    have hsigned : Int.toNat ((Fintype.card ι : ℤ) -
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) =
        Fintype.card ι - Int.toNat
          (Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) := by
      omega
    rw [hsigned]
    exact WithTop.coe_le_coe.mpr hweight
  · have hnegative : Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G < 0 :=
      lt_of_not_ge hdegree
    have hspace : GlobalPlace.riemannRochSubmodule G = ⊥ :=
      GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree k F G hnegative
    have hcode : (agEvaluationCode G Q hG).carrier = ⊥ := by
      change (agEvaluationLinearMap G Q hG).range = ⊥
      apply le_antisymm
      · rintro x ⟨f, rfl⟩
        change agEvaluationLinearMap G Q hG f = 0
        have hfzero : (f : F) = 0 := by
          have hmemBot : (f : F) ∈ (⊥ : Submodule k F) := by
            rw [← hspace]
            exact f.property
          exact (Submodule.mem_bot k).mp hmemBot
        have hfsubtype : f = 0 := by
          apply Subtype.ext
          exact hfzero
        simpa [hfsubtype]
      · exact bot_le
    rw [(QEC.Coding.HypergraphProduct.extendedMinimumDistance_eq_top_iff _).mpr hcode]
    exact le_top
end QEC.Coding.AlgebraicGeometry

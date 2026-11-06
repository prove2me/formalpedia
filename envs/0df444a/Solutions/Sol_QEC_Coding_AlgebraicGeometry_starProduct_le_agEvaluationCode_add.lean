-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.starProduct_le_agEvaluationCode_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:45.000241+00:00
-- url     : https://prove2.me/submissions/802c343e-5ec4-4b73-bee6-cbdcb7d4af29

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mul_mem_riemannRochSubmodule_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
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
section
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
private theorem evaluationRegularityOfMem (G : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0)
    (f : GlobalPlace.riemannRochSubmodule G) (i : ι) :
    GlobalPlace.RegularAt (Q i).place (f : F) := by
  have hbound : (Q i).place.valuation (f : F) ≤ WithZero.exp (G (Q i).place) :=
    (GlobalPlace.mem_riemannRochSubmodule_iff G (f : F)).mp f.property (Q i).place
  rw [hG i] at hbound
  rw [WithZero.exp_zero] at hbound
  exact hbound
private theorem rational_evaluateRegular_mul (Q : RationalPlace k F)
    (f g : F) (hf : GlobalPlace.RegularAt Q.place f)
    (hg : GlobalPlace.RegularAt Q.place g)
    (hfg : GlobalPlace.RegularAt Q.place (f * g)) :
    Q.evaluateRegular (f * g) hfg =
      Q.evaluateRegular f hf * Q.evaluateRegular g hg := by
  let xf : GlobalPlace.valuationRing Q.place :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let xg : GlobalPlace.valuationRing Q.place :=
    ⟨g, (GlobalPlace.mem_valuationRing_iff Q.place g).mpr hg⟩
  let xfg : GlobalPlace.valuationRing Q.place :=
    ⟨f * g, (GlobalPlace.mem_valuationRing_iff Q.place (f * g)).mpr hfg⟩
  change Q.evaluate xfg = Q.evaluate xf * Q.evaluate xg
  have hmul : xfg = xf * xg := by
    rfl
  rw [hmul]
  exact Q.evaluate.map_mul xf xg
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [Fintype k]
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hG : ∀ i, G (Q i).place = 0)
    (hH : ∀ i, H (Q i).place = 0) :
    agStarProduct (agEvaluationCode G Q hG) (agEvaluationCode H Q hH) ≤
      (agEvaluationCode (G + H) Q (evaluationSupport_add G H Q hG hH)).carrier := by
  apply Submodule.span_le.mpr
  rintro w ⟨x, hx, y, hy, rfl⟩
  change x ∈ (agEvaluationLinearMap G Q hG).range at hx
  change y ∈ (agEvaluationLinearMap H Q hH).range at hy
  rcases hx with ⟨f, rfl⟩
  rcases hy with ⟨g, rfl⟩
  let hGH : ∀ i, (G + H) (Q i).place = 0 := evaluationSupport_add G H Q hG hH
  let fg : GlobalPlace.riemannRochSubmodule (G + H) :=
    ⟨(f : F) * (g : F),
      GlobalPlace.mul_mem_riemannRochSubmodule_add f.property g.property⟩
  change agWordStar (agEvaluationLinearMap G Q hG f)
      (agEvaluationLinearMap H Q hH g) ∈
        (agEvaluationLinearMap (G + H) Q hGH).range
  refine ⟨fg, ?_⟩
  ext i
  simp only [agEvaluationLinearMap_apply, agWordStar_apply]
  change (Q i).evaluateRegular ((f : F) * (g : F)) _ =
    (Q i).evaluateRegular (f : F) _ * (Q i).evaluateRegular (g : F) _
  exact rational_evaluateRegular_mul (Q i) (f : F) (g : F)
    (evaluationRegularityOfMem G Q hG f i)
    (evaluationRegularityOfMem H Q hH g i)
    (evaluationRegularityOfMem (G + H) Q hGH fg i)
end QEC.Coding.AlgebraicGeometry

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agEvaluation_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:57.816193+00:00
-- url     : https://prove2.me/submissions/55b33dfa-5946-481a-9e0a-1ed9cf7716e9

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_degree_eq_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZero_mem_riemannRochSubmodule_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_eq_bot_of_negative_degree
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (hdegree : Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G <
      Fintype.card ι) :
    Function.Injective (agEvaluationLinearMap G Q hG) := by
  intro f g hfg
  apply Subtype.ext
  have hzero : agEvaluationLinearMap G Q hG (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hmem : ((f - g : GlobalPlace.riemannRochSubmodule G) : F) ∈
      GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) :=
    evaluationZero_mem_riemannRochSubmodule_sub G Q hQ hG (f - g) hzero
  have hnegative :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (G - evaluationDivisor Q) < 0 := by
    rw [Divisor.degree_sub, evaluationDivisor_degree_eq_card]
    omega
  have hbot := GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
    k F (G - evaluationDivisor Q) hnegative
  have hsub : ((f - g : GlobalPlace.riemannRochSubmodule G) : F) = 0 := by
    have hmem_bot : ((f - g : GlobalPlace.riemannRochSubmodule G) : F) ∈
        (⊥ : Submodule k F) := by
      rw [← hbot]
      exact hmem
    exact (Submodule.mem_bot k).mp hmem_bot
  exact sub_eq_zero.mp hsub
end QEC.Coding.AlgebraicGeometry

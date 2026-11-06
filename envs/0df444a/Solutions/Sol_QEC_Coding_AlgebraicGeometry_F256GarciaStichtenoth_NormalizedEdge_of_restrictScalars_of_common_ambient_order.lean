-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.of_restrictScalars_of_common_ambient_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:18:41.80824+00:00
-- url     : https://prove2.me/submissions/f7223420-b42f-443b-982b-09ba8fdd7f62

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_intermediatePrime_order_eq_of_common_ambient_order

set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A B F K E : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [_root_.Field F] [_root_.Field K] [_root_.Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [Algebra A F] [IsFractionRing A F] [Algebra A E] [IsScalarTower A F E]
    [Algebra B K] [IsFractionRing B K] [Algebra B E] [IsScalarTower B K E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [Algebra F256 F] [Algebra F256 K] [Algebra F256 E]
    [IsScalarTower F256 F E] [IsScalarTower F256 K E]
    [Module.Finite A (integralClosure A E)] [Module.Finite B (integralClosure B E)]
    [IsDedekindDomain (integralClosure A E)] [IsDedekindDomain (integralClosure B E)]
    [IsFractionRing (integralClosure A E) E] [IsFractionRing (integralClosure B E) E]
    (QA : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
    (QB : IsDedekindDomain.HeightOneSpectrum (integralClosure B E))
local notation "CA" => IntermediateIntegralModels.Model A F E
local notation "CB" => IntermediateIntegralModels.Model B K E
local notation "PA" => IntermediateIntegralModels.prime A F E QA
local notation "PB" => IntermediateIntegralModels.prime B K E QB
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace NormalizedEdge
theorem _root_.solution
    (hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order)
    {J L : IntermediateField K E}
    (h : NormalizedEdge A F E QA (J.restrictScalars F) (L.restrictScalars F)) :
    NormalizedEdge B K E QB J L := by
  obtain ⟨a, y, hy, ha, hgen⟩ := h
  refine ⟨a, y, hy, ?_, ?_⟩
  · rw [intermediatePrime_order_eq_of_common_ambient_order A B F K E QA QB hupper J] at ha
    exact ha
  · apply IntermediateField.restrictScalars_injective F
    exact hgen
end NormalizedEdge
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

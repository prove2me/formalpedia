-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedRefinement.of_restrictScalars_of_common_ambient_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:20:53.546192+00:00
-- url     : https://prove2.me/submissions/b6e6d9ea-b891-4bd3-bd7a-6c65bc15dc9e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_of_restrictScalars_of_common_ambient_order

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
namespace NormalizedRefinement
theorem _root_.solution
    (hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order)
    {J L : IntermediateField K E}
    (h : NormalizedRefinement A F E QA (J.restrictScalars F) (L.restrictScalars F)) :
    NormalizedRefinement B K E QB J L := by
  have hlift (N : IntermediateField F E)
      (hchain : NormalizedRefinement A F E QA (J.restrictScalars F) N) :
      ∃ N' : IntermediateField K E, N'.restrictScalars F = N ∧
        NormalizedRefinement B K E QB J N' := by
    induction hchain with
    | refl => exact ⟨J, rfl, .refl⟩
    | @tail N M hchain hstep ih =>
        obtain ⟨N', hN', ih⟩ := ih
        have hJM := NormalizedRefinement.le A F E QA (hchain.tail hstep)
        let M' : IntermediateField K E :=
          M.toSubfield.toIntermediateField (fun x => hJM (J.algebraMap_mem x))
        have hedge : NormalizedEdge A F E QA (N'.restrictScalars F) (M'.restrictScalars F) := by
          change NormalizedEdge A F E QA (N'.restrictScalars F) M
          rwa [hN']
        exact ⟨M', rfl, ih.tail
          (hedge.of_restrictScalars_of_common_ambient_order A B F K E QA QB hupper)⟩
  obtain ⟨L', hL', hchain⟩ := hlift _ h
  have heq : L' = L := IntermediateField.restrictScalars_injective F hL'
  rwa [heq] at hchain
end NormalizedRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

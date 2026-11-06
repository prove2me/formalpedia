-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediatePrime_order_eq_of_common_ambient_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:16:20.759199+00:00
-- url     : https://prove2.me/submissions/bc5ccf90-1553-4c7c-9a7e-b0b9b083e5a2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_eq_of_common_extension


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
theorem _root_.solution
    (hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order)
    (J : IntermediateField K E) :
    (heightOnePlace (k := F256) (K := J.restrictScalars F) (PA (J.restrictScalars F))).order =
      (heightOnePlace (k := F256) (K := J) (PB J)).order := by
  let JA := J.restrictScalars F
  letI : Algebra (CA JA) J := inferInstanceAs (Algebra (CA JA) JA)
  letI : IsFractionRing (CA JA) J := inferInstanceAs (IsFractionRing (CA JA) JA)
  letI : IsScalarTower (CA JA) J E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (CA JA) (integralClosure A E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (CB J) (integralClosure B E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : QA.asIdeal.LiesOver (PA JA).asIdeal := ⟨rfl⟩
  letI : QB.asIdeal.LiesOver (PB J).asIdeal := ⟨rfl⟩
  exact heightOnePlace_order_eq_of_common_extension
    (k := F256) (K := J) (L := E) (PA JA) (PB J) QA QB hupper
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

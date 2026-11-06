-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedRefinement.integralClosure_differentialGeneratorOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:25:52.571845+00:00
-- url     : https://prove2.me/submissions/6b324861-2f2a-43c8-aec8-4938f71d2284

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_differentialGeneratorOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_differentialGeneratorOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_unramified_order_transport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ramificationIdx_and_weakDifferent_of_finrank_eq_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Algebra (RatFunc F256) F] [Algebra (RatFunc F256) E]
    [IsScalarTower F256 (RatFunc F256) F] [IsScalarTower F256 (RatFunc F256) E]
    [IsScalarTower (RatFunc F256) F E]
    [FiniteDimensional (RatFunc F256) F] [Algebra.IsSeparable (RatFunc F256) F]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateRationalConstantTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateRationalRelativeTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateConstantRelativeTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateRationalFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateRationalSeparable
local notation "g" => intermediateDifferentialGeneratorOrder A F E Q
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace NormalizedRefinement
theorem _root_.solution
    [FiniteDimensional (RatFunc F256) E] [Algebra.IsSeparable (RatFunc F256) E]
    [Module.IsTorsionFree A E] [IsDedekindDomain (integralClosure A E)]
    [IsFractionRing (integralClosure A E) E]
    (h : NormalizedRefinement A F E Q ⊥ ⊤) :
    differentialOrder (heightOnePlace (k := F256) (K := E) Q)
      (functionFieldDifferentialGenerator (k := F256) (F := E))
      functionFieldDifferentialGenerator_ne_zero =
    ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) *
      differentialOrder (heightOnePlace (k := F256) (K := F) (Q.under A))
        (functionFieldDifferentialGenerator (k := F256) (F := F))
        functionFieldDifferentialGenerator_ne_zero +
      2 * (((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) - 1) := by
  let K : IntermediateField F E := ⊥
  let L : IntermediateField F E := ⊤
  let C₀ := C K
  let C₁ := C L
  let P₀ := P K
  let P₁ := P L
  let p := Q.under A
  letI : Fact (K ≤ L) := ⟨bot_le⟩
  letI : Module.IsTorsionFree A (integralClosure A E) := IsIntegralClosure.isTorsionFree A E
  letI : P₀.asIdeal.LiesOver p.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change Ideal.comap (algebraMap A (integralClosure A E)) Q.asIdeal =
      Ideal.comap (algebraMap A C₀) (Ideal.comap (algebraMap C₀ (integralClosure A E)) Q.asIdeal)
    rw [Ideal.comap_comap]
    rfl
  letI : Q.asIdeal.LiesOver P₁.asIdeal := ⟨rfl⟩
  letI : P₁.asIdeal.LiesOver p.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change Ideal.comap (algebraMap A (integralClosure A E)) Q.asIdeal =
      Ideal.comap (algebraMap A C₁) (Ideal.comap (algebraMap C₁ (integralClosure A E)) Q.asIdeal)
    rw [Ideal.comap_comap]
    rfl
  letI : Module.IsTorsionFree C₁ (integralClosure A E) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Algebra C₁ E := ((algebraMap L E).comp (algebraMap C₁ L)).toAlgebra
  letI : IsScalarTower C₁ L E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower C₁ (integralClosure A E) E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F256 F K := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply F256 F E c)
  letI : IsScalarTower (RatFunc F256) F K := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply (RatFunc F256) F E c)
  letI : IsScalarTower F256 L E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (RatFunc F256) L E := IsScalarTower.of_algebraMap_eq' rfl
  have he₀ := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    A C₀ F K p P₀ IntermediateField.finrank_bot).1
  have hetop := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    C₁ (integralClosure A E) L E P₁ Q IntermediateField.finrank_top).1
  have h₀ := differentialGenerator_order_of_unramified_order_transport
    (heightOnePlace (k := F256) (K := F) p) (heightOnePlace (k := F256) (K := K) P₀)
    (fun x hx => by
      simpa only [he₀, Nat.cast_one, one_mul] using
        heightOnePlace_order_algebraMap (k := F256) (K := F) (L := K) p P₀ x hx)
  have htop := differentialGenerator_order_of_unramified_order_transport
    (heightOnePlace (k := F256) (K := L) P₁) (heightOnePlace (k := F256) (K := E) Q)
    (fun x hx => by
      simpa only [hetop, Nat.cast_one, one_mul] using
        heightOnePlace_order_algebraMap (k := F256) (K := L) (L := E) P₁ Q x hx)
  have hchain := NormalizedRefinement.differentialGeneratorOrder A F E Q h
  change g K = _ at h₀
  change _ = g L at htop
  have he : p.asIdeal.ramificationIdx' Q.asIdeal = P₀.asIdeal.ramificationIdx' P₁.asIdeal := by
    rw [Ideal.ramificationIdx_algebra_tower' p.asIdeal P₁.asIdeal Q.asIdeal, hetop, mul_one,
      Ideal.ramificationIdx_algebra_tower' p.asIdeal P₀.asIdeal P₁.asIdeal, he₀, one_mul]
  rw [htop, hchain, h₀, he]
end NormalizedRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

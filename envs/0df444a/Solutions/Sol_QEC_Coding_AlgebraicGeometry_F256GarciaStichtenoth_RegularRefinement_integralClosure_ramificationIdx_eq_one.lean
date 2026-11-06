-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.integralClosure_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:40:17.48947+00:00
-- url     : https://prove2.me/submissions/fc2eb680-bf69-4db5-adcb-b2a3d31be7eb

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinementRamification
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_ramificationIdx_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_ramificationIdx_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ramificationIdx_and_weakDifferent_of_finrank_eq_one


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
    [IsFractionRing (integralClosure A E) E]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
local notation "R" => heightOnePlace (k := F256) (K := E) Q
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace RegularRefinement
theorem _root_.solution
    [Module.IsTorsionFree A E]
    (h : RegularRefinement R (⊥ : IntermediateField F E) ⊤) :
    (Q.under A).asIdeal.ramificationIdx' Q.asIdeal = 1 := by
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
  have h₀ := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    A C₀ F K p P₀ IntermediateField.finrank_bot).1
  have h₁ := RegularRefinement.ramificationIdx_eq_one A F E Q h
  have htop := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    C₁ (integralClosure A E) L E P₁ Q IntermediateField.finrank_top).1
  change p.asIdeal.ramificationIdx' Q.asIdeal = 1
  rw [Ideal.ramificationIdx_algebra_tower' p.asIdeal P₁.asIdeal Q.asIdeal, htop, mul_one,
    Ideal.ramificationIdx_algebra_tower' p.asIdeal P₀.asIdeal P₁.asIdeal, h₀, h₁, one_mul]
end RegularRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

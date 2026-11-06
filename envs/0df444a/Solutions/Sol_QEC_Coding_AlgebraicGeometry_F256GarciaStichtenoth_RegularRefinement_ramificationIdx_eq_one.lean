-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:29:13.143516+00:00
-- url     : https://prove2.me/submissions/cc31fff4-f495-48a7-b699-b06e7909954e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinementRamification
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_ramificationIdx_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
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
    {K L : IntermediateField F E} (h : RegularRefinement R K L) :
    letI : Fact (K ≤ L) := ⟨h.le R⟩
    (P K).asIdeal.ramificationIdx' (P L).asIdeal = 1 := by
  induction h with
  | refl =>
      letI : Fact (K ≤ K) := ⟨le_rfl⟩
      have hid : algebraMap (C K) (C K) = RingHom.id (C K) := by
        apply RingHom.ext
        intro x
        rfl
      have hmap : Ideal.map (algebraMap (C K) (C K)) (P K).asIdeal = (P K).asIdeal := by
        rw [hid, Ideal.map_id]
      have he := Ideal.ramificationIdx_map_self_eq_one (p := (P K).asIdeal)
        (by rw [hmap]; exact (P K).isPrime.ne_top) (by rw [hmap]; exact (P K).ne_bot)
      simp only [hmap] at he ⊢
      exact he
  | @tail L M hchain hstep ih =>
      letI : Fact (K ≤ L) := ⟨RegularRefinement.le R hchain⟩
      letI : Fact (L ≤ M) := ⟨hstep.le R⟩
      letI : Fact (K ≤ M) := ⟨(RegularRefinement.le R hchain).trans (hstep.le R)⟩
      rw [Ideal.ramificationIdx_algebra_tower' (P K).asIdeal (P L).asIdeal (P M).asIdeal,
        ih, hstep.ramificationIdx_eq_one A F E Q, one_mul]
end RegularRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

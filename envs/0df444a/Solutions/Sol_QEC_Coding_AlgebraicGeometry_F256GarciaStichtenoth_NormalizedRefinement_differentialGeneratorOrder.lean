-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedRefinement.differentialGeneratorOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:22:48.475268+00:00
-- url     : https://prove2.me/submissions/d33c8608-ad62-4ad7-a9e1-0f952991acb7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_differentialGeneratorOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_normalizedEdge_refl


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
omit [IsScalarTower F256 (RatFunc F256) F]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace NormalizedRefinement
theorem _root_.solution
    {K L : IntermediateField F E} (h : NormalizedRefinement A F E Q K L) :
    letI : Fact (K ≤ L) := ⟨h.le A F E Q⟩
    g L = ((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) * g K +
      2 * (((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) - 1) := by
  induction h with
  | refl =>
      letI : Fact (K ≤ K) := ⟨le_rfl⟩
      exact NormalizedEdge.differentialGeneratorOrder A F E Q (normalizedEdge_refl A F E Q K)
  | @tail L M hchain hstep ih =>
      letI : Fact (K ≤ L) := ⟨NormalizedRefinement.le A F E Q hchain⟩
      letI : Fact (L ≤ M) := ⟨hstep.le A F E Q⟩
      letI : Fact (K ≤ M) :=
        ⟨(NormalizedRefinement.le A F E Q hchain).trans (hstep.le A F E Q)⟩
      rw [hstep.differentialGeneratorOrder A F E Q, ih,
        Ideal.ramificationIdx_algebra_tower' (P K).asIdeal (P L).asIdeal (P M).asIdeal,
        Nat.cast_mul]
      ring
end NormalizedRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

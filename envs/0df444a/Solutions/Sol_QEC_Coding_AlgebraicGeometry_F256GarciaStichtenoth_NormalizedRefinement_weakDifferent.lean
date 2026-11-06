-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedRefinement.weakDifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:19:17.331734+00:00
-- url     : https://prove2.me/submissions/42835a54-3109-4a44-aea0-992678608e44

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_self_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_weakDifferent_tower_of_fractionFields


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
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace NormalizedRefinement
theorem _root_.solution
    {K L : IntermediateField F E}
    (h : NormalizedRefinement A F E Q K L) :
    letI : Fact (K ≤ L) := ⟨h.le A F E Q⟩
    multiplicity (P L).asIdeal (differentIdeal (C K) (C L)) =
      2 * ((P K).asIdeal.ramificationIdx' (P L).asIdeal - 1) := by
  induction h with
  | refl =>
      letI : Fact (K ≤ K) := ⟨le_rfl⟩
      exact self_weakDifferent (C K) (P K)
  | @tail L M hchain hstep ih =>
      letI : Fact (K ≤ L) := ⟨NormalizedRefinement.le A F E Q hchain⟩
      letI : Fact (L ≤ M) := ⟨hstep.le A F E Q⟩
      letI : Fact (K ≤ M) :=
        ⟨(NormalizedRefinement.le A F E Q hchain).trans (hstep.le A F E Q)⟩
      exact weakDifferent_tower_of_fractionFields
        (C K) (C L) (C M) K M (P K) (P L) (P M)
        ih (hstep.weakDifferent A F E Q)
end NormalizedRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

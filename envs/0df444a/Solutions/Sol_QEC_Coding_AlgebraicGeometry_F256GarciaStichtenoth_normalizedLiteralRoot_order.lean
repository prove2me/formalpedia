-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.normalizedLiteralRoot_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:19:15.681505+00:00
-- url     : https://prove2.me/submissions/cba7cf61-c83f-4558-ad15-d1f9c04984cc

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_literalQuadratic_finrank_eq_one_or_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_artinSchreier_order_dichotomy_of_finrank_le_two


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
theorem _root_.solution
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) (P K)).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a) :
    (heightOnePlace (k := F256) (K := L) (P L)).order y = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := L) (P L)).order y := by
  have hdeg := literalQuadratic_finrank_eq_one_or_two a y hy hgen
  letI : FaithfulSMul (C K) (C L) :=
    Module.isTorsionFree_iff_faithfulSMul.mp
      (IntermediateIntegralModels.modelRelativeTorsionFree A F E K L)
  exact heightOnePlace_artinSchreier_order_dichotomy_of_finrank_le_two
    (P K) (P L) a y hy (by omega) ha
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.weakDifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:12:50.290933+00:00
-- url     : https://prove2.me/submissions/3b415c4c-2ba5-4b5b-be6c-a5e7a14bd64c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_in_subfield_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_literalQuadratic_finrank_eq_one_or_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_integralModel_weakDifferent
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
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace NormalizedEdge
theorem _root_.solution
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (h : NormalizedEdge A F E Q K L) :
    multiplicity (P L).asIdeal (differentIdeal (C K) (C L)) =
      2 * ((P K).asIdeal.ramificationIdx' (P L).asIdeal - 1) := by
  obtain ⟨a, y, hy, ha, hL⟩ := h
  have hyL : y ∈ L := by
    rw [← hL]
    exact IntermediateField.mem_adjoin_simple_self K y
  let yL : L := ⟨y, hyL⟩
  have heq : yL ^ 2 + yL = algebraMap K L a := by
    apply Subtype.ext
    exact hy
  have hgen := adjoin_in_subfield_eq_top K L y hyL hL
  rcases literalQuadratic_finrank_eq_one_or_two a yL heq hgen with hdeg | hdeg
  · exact (ramificationIdx_and_weakDifferent_of_finrank_eq_one
      (C K) (C L) K L (P K) (P L) hdeg).2
  · exact quadraticLiteral_integralModel_weakDifferent
      A (C K) (C L) K L (P K) (P L) a yL heq hdeg hgen ha
end NormalizedEdge
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

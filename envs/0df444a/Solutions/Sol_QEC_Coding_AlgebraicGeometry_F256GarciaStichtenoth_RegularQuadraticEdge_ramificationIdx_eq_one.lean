-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularQuadraticEdge.ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:27:23.340323+00:00
-- url     : https://prove2.me/submissions/e90f67ae-eb8b-4e6b-af58-a94f4ec1e320

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinementRamification
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_intermediatePrime_order_nonnegative_of_ambient_regular
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_in_subfield_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_literalQuadratic_finrank_eq_one_or_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_integralModel_ramificationIdx_eq_one
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
namespace RegularQuadraticEdge
theorem _root_.solution
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (h : RegularQuadraticEdge R K L) : (P K).asIdeal.ramificationIdx' (P L).asIdeal = 1 := by
  obtain ⟨y, hy, ha, hL⟩ := h
  let a : K := ⟨y ^ 2 + y, ha⟩
  have hyL : y ∈ L := by
    rw [hL]
    exact (show F⟮y⟯ ≤ K ⊔ F⟮y⟯ from le_sup_right) (mem_adjoin_simple_self F y)
  let yL : L := ⟨y, hyL⟩
  have heq : yL ^ 2 + yL = algebraMap K L a := Subtype.ext rfl
  have hgen := adjoin_in_subfield_eq_top K L y hyL (by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, ← hL])
  have hareg : 0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a :=
    intermediatePrime_order_nonnegative_of_ambient_regular A F E Q K a
      ((R).valuationRing.add_mem _ _ ((R).valuationRing.pow_mem hy 2) hy)
  rcases literalQuadratic_finrank_eq_one_or_two a yL heq hgen with hdeg | hdeg
  · exact (ramificationIdx_and_weakDifferent_of_finrank_eq_one
      (C K) (C L) K L (P K) (P L) hdeg).1
  · exact quadraticLiteral_integralModel_ramificationIdx_eq_one
      A (C K) (C L) K L (P K) (P L) a yL heq hdeg hgen hareg
end RegularQuadraticEdge
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

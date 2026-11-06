-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.differentialGeneratorOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:16:35.09288+00:00
-- url     : https://prove2.me/submissions/7fd52f39-94ff-4e4a-8834-fe169ea5fc19

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_in_subfield_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_literalQuadratic_finrank_eq_one_or_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_integralModel_ramificationIdx_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_quadratic_simplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_unramified_order_transport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_of_simplePole
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
omit [IsScalarTower F256 (RatFunc F256) F]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace NormalizedEdge
theorem _root_.solution
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (h : NormalizedEdge A F E Q K L) :
    g L = ((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) * g K +
      2 * (((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) - 1) := by
  letI : FaithfulSMul (C K) (C L) :=
    Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  letI : NoZeroSMulDivisors (C K) (C L) := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  let Pk := heightOnePlace (k := F256) (K := K) (P K)
  let Pl := heightOnePlace (k := F256) (K := L) (P L)
  let e := (P K).asIdeal.ramificationIdx' (P L).asIdeal
  have horder (x : K) (hx : x ≠ 0) : Pl.order (algebraMap K L x) = (e : ℤ) * Pk.order x :=
    heightOnePlace_order_algebraMap (k := F256) (K := K) (L := L) (P K) (P L) x hx
  have hregular (he : e = 1) : g L = (e : ℤ) * g K + 2 * ((e : ℤ) - 1) := by
    rw [he]
    simp only [Nat.cast_one, one_mul, sub_self, mul_zero, add_zero]
    exact differentialGenerator_order_of_unramified_order_transport Pk Pl
      (fun x hx => by simpa only [he, Nat.cast_one, one_mul] using horder x hx)
  obtain ⟨a, y, hy, ha, hL⟩ := h
  have hyL : y ∈ L := by
    rw [← hL]
    exact mem_adjoin_simple_self K y
  let yL : L := ⟨y, hyL⟩
  have heq : yL ^ 2 + yL = algebraMap K L a := Subtype.ext hy
  have hgen := adjoin_in_subfield_eq_top K L y hyL hL
  rcases literalQuadratic_finrank_eq_one_or_two a yL heq hgen with hdeg | hdeg
  · exact hregular (ramificationIdx_and_weakDifferent_of_finrank_eq_one
      (C K) (C L) K L (P K) (P L) hdeg).1
  · rcases ha with hpole | hreg
    · have ha0 : a ≠ 0 := by
        intro hz
        simp [hz, GlobalPlace.order] at hpole
      have hepos : 0 < e := Nat.pos_iff_ne_zero.mpr
        (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver (P L).asIdeal (P K).ne_bot)
      have hele : e ≤ 2 := (Ideal.ramificationIdx_le_finrank (C L) K L (P L).asIdeal).trans_eq hdeg
      have hyorder := (Pk.artinSchreier_root_order_of_simplePole Pl a yL e
        hepos hele heq (horder a ha0) hpole).2
      letI : CharP F256 2 :=
        charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
      letI : CharP L 2 := charP_of_injective_algebraMap (algebraMap F256 L).injective 2
      exact differentialGenerator_order_of_quadratic_simplePole Pk Pl e horder a yL hpole hyorder heq
    · exact hregular (quadraticLiteral_integralModel_ramificationIdx_eq_one
        A (C K) (C L) K L (P K) (P L) a yL heq hdeg hgen hreg)
end NormalizedEdge
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

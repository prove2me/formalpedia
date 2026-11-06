-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierCoordinate_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:49:16.906447+00:00
-- url     : https://prove2.me/submissions/e9f31390-595d-42de-9750-7c2c825b724d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierReciprocalRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierReciprocalRoot_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierCoordinate P a ha ^ 2 +
        quadraticArtinSchreierCoordinate P a ha =
      quadraticArtinSchreierEmbedding P a ha a := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (QuadraticArtinSchreierField P a ha) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (QuadraticArtinSchreierField P a ha)).injective 2
  let b := quadraticArtinSchreierEmbedding P a ha a
  let w := quadraticArtinSchreierReciprocalRoot P a ha
  have hb : b ≠ 0 := by
    have hport := (quadraticArtinSchreierEmbedding P a ha).injective.ne
      (quadraticArtinSchreier_parameter_ne_zero P a ha)
    simp only [b, map_zero] at hport ⊢
    exact hport
  have hw : w ≠ 0 := quadraticArtinSchreierReciprocalRoot_ne_zero P a ha
  have hroot := quadraticArtinSchreierReciprocalRoot_equation P a ha
  rw [map_inv₀] at hroot
  change w ^ 2 + b⁻¹ * w + b⁻¹ = 0 at hroot
  field_simp [hb] at hroot
  change w⁻¹ ^ 2 + w⁻¹ = b
  field_simp [hw]
  have htwo : (2 : QuadraticArtinSchreierField P a ha) = 0 :=
    CharP.cast_eq_zero (QuadraticArtinSchreierField P a ha) 2
  linear_combination hroot - b * w ^ 2 * htwo
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

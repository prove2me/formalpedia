-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_evaluate_stepDistinguishedCoordinate_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:40.830811+00:00
-- url     : https://prove2.me/submissions/742cf2d5-0da0-4e85-a492-f432a71f5e5e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryCoordinate_artinSchreier
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluateRegular_eq_zero_iff
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem stepEmbeddedCoordinate_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepFieldEmbedding P x hx x ≠ 0 := by
  have hxne : x ≠ 0 := by
    intro hzero
    subst x
    norm_num [GlobalPlace.order] at hx
  intro hmap
  apply hxne
  apply (stepFieldEmbedding P x hx).injective
  simp only [map_zero] at hmap ⊢
  exact hmap
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hvalue : Q.evaluateRegular x hregular ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (splitUpperRationalPlace Q P x hx hregular c).evaluateRegular
        (stepDistinguishedCoordinate P x hx)
        (splitAbovePlace_stepDistinguishedCoordinate_regular
          Q P x hx hregular hvalue c) ≠ 0 := by
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  let U := splitUpperRationalPlace Q P x hx hregular c
  let y := stepDistinguishedCoordinate P x hx
  let z := stepAuxiliaryCoordinate P x hx
  let xL := stepFieldEmbedding P x hx x
  have hyregular := splitAbovePlace_stepDistinguishedCoordinate_regular
    Q P x hx hregular hvalue c
  have hxval := splitAbovePlace_embeddedCoordinate_valuation_eq_one
    Q P x hx hregular hvalue c
  intro hyevaluate
  have hylt : H.valuation L y < 1 := by
    have hymem : (⟨y,
        (GlobalPlace.mem_valuationRing_iff U.place y).mpr hyregular⟩ :
          U.place.valuationRing) ∈
        IsLocalRing.maximalIdeal U.place.valuationRing :=
      (U.evaluateRegular_eq_zero_iff y hyregular).1 hyevaluate
    rw [Valuation.mem_maximalIdeal_iff] at hymem
    exact hymem
  have hxL_ne : xL ≠ 0 := stepEmbeddedCoordinate_ne_zero P x hx
  have hxval' : H.valuation L xL = 1 := hxval
  have hyx : y * xL = z := by
    dsimp [y, z, xL]
    rw [stepDistinguishedCoordinate]
    exact div_mul_cancel₀ _ hxL_ne
  have hzlt : H.valuation L z < 1 := by
    calc
      H.valuation L z = H.valuation L (y * xL) := by rw [hyx]
      _ = H.valuation L y * H.valuation L xL := (H.valuation L).map_mul _ _
      _ = H.valuation L y := by rw [hxval', mul_one]
      _ < 1 := hylt
  have hzpowlt : H.valuation L (z ^ 16) < 1 := by
    rw [(H.valuation L).map_pow]
    exact pow_lt_one₀ zero_le' hzlt (by norm_num)
  have hleftlt : H.valuation L (z ^ 16 + z) < 1 :=
    lt_of_le_of_lt ((H.valuation L).map_add _ _) (max_lt hzpowlt hzlt)
  have hright : H.valuation L (xL ^ 17) = 1 := by
    rw [(H.valuation L).map_pow, hxval', one_pow]
  have hequation : z ^ 16 + z = xL ^ 17 := by
    exact stepAuxiliaryCoordinate_artinSchreier P x hx
  rw [hequation, hright] at hleftlt
  exact lt_irrefl 1 hleftlt
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

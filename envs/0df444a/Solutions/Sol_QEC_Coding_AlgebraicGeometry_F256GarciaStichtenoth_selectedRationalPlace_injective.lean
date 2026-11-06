-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:06:59.494617+00:00
-- url     : https://prove2.me/submissions/e16a9c9e-431b-4ee0-88fc-994d292ca2c5

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluateRegular_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_normalizedValuation_eq_of_isEquiv
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem globalPlace_eq_of_valuation_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (P Q : GlobalPlace F256 E) (h : P.valuation = Q.valuation) : P = Q := by
  cases P with
  | mk pv hp =>
      cases Q with
      | mk qv hq =>
          dsimp at h
          subst qv
          rfl
private theorem rationalPlace_eq_of_place_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (P Q : RationalPlace F256 E) (h : P.place = Q.place) : P = Q := by
  cases P with
  | mk pp pe ph =>
      cases Q with
      | mk qp qe qh =>
          dsimp at h
          subst qp
          have he : pe = qe := by
            apply RingEquiv.ext
            intro a
            rw [ph, qh]
          subst qe
          rfl
private theorem splitAbovePlace_stepEmbedding_regular_iff
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (Q : RationalPlace F256 E) (P : GlobalPlace F256 E) (x : E)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) (f : E) :
    GlobalPlace.RegularAt (splitAbovePlace Q P x hx c)
        (stepFieldEmbedding P x hx f) ↔
      GlobalPlace.RegularAt Q.place f := by
  refine ⟨?_, splitAbovePlace_stepEmbedding_regular Q P x hx c f⟩
  intro hupper
  by_contra hbase
  have hgt : 1 < Q.place.valuation f := lt_of_not_ge hbase
  have hfne : f ≠ 0 := by
    intro hfzero
    subst f
    simp at hgt
  have hinvlt : Q.place.valuation f⁻¹ < 1 := by
    rw [Q.place.valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ hgt
  have hinvregular : GlobalPlace.RegularAt Q.place f⁻¹ := hinvlt.le
  let U := splitUpperRationalPlace Q P x hx hregular c
  have hinvupper := splitAbovePlace_stepEmbedding_regular
    Q P x hx c f⁻¹ hinvregular
  have hinvevaluate := splitUpperRationalPlace_evaluate_stepEmbedding
    Q P x hx hregular c f⁻¹ hinvregular
  have hinvzero : U.evaluateRegular
      (stepFieldEmbedding P x hx f⁻¹) hinvupper = 0 := by
    rw [hinvevaluate, Q.evaluateRegular_eq_zero_iff,
      Valuation.mem_maximalIdeal_iff]
    exact hinvlt
  let uf : U.place.valuationRing :=
    ⟨stepFieldEmbedding P x hx f,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr hupper⟩
  let uinv : U.place.valuationRing :=
    ⟨stepFieldEmbedding P x hx f⁻¹,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr hinvupper⟩
  have hproduct : uf * uinv = 1 := by
    apply Subtype.ext
    change stepFieldEmbedding P x hx f *
        stepFieldEmbedding P x hx f⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hfne, map_one]
  have hevaluate := congrArg U.evaluate hproduct
  rw [map_mul, map_one] at hevaluate
  change U.evaluateRegular (stepFieldEmbedding P x hx f) hupper *
      U.evaluateRegular (stepFieldEmbedding P x hx f⁻¹) hinvupper = 1 at hevaluate
  rw [hinvzero, mul_zero] at hevaluate
  exact zero_ne_one hevaluate
private theorem splitUpperRationalPlace_parent_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (Q R : RationalPlace F256 E) (P : GlobalPlace F256 E) (x : E)
    (hx : P.order x = -1)
    (hQregular : GlobalPlace.RegularAt Q.place x)
    (hRregular : GlobalPlace.RegularAt R.place x)
    (c d : LinearMap.ker f256ArtinSchreier)
    (hupper : splitUpperRationalPlace Q P x hx hQregular c =
      splitUpperRationalPlace R P x hx hRregular d) : Q = R := by
  have hplace : splitAbovePlace Q P x hx c =
      splitAbovePlace R P x hx d :=
    congrArg RationalPlace.place hupper
  have hregular_iff (f : E) : GlobalPlace.RegularAt Q.place f ↔
      GlobalPlace.RegularAt R.place f := by
    constructor
    · intro hf
      have hu := splitAbovePlace_stepEmbedding_regular Q P x hx c f hf
      rw [hplace] at hu
      exact (splitAbovePlace_stepEmbedding_regular_iff
        R P x hx hRregular d f).mp hu
    · intro hf
      have hu := splitAbovePlace_stepEmbedding_regular R P x hx d f hf
      rw [← hplace] at hu
      exact (splitAbovePlace_stepEmbedding_regular_iff
        Q P x hx hQregular c f).mp hu
  have hisEquiv : Q.place.valuation.IsEquiv R.place.valuation :=
    (Valuation.isEquiv_iff_val_le_one).2 fun {f} => hregular_iff f
  have hvaluation : Q.place.valuation = R.place.valuation :=
    normalizedValuation_eq_of_isEquiv
      Q.place.valuation R.place.valuation
      Q.place.normalized R.place.normalized hisEquiv
  exact rationalPlace_eq_of_place_eq Q R
    (globalPlace_eq_of_valuation_eq Q.place R.place hvaluation)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution :
    ∀ i : ℕ, Function.Injective (selectedRationalPlace i)
  | 0 => by
      intro a b hab
      apply baseRationalPlace_injective
      exact congrArg RationalPlace.place hab
  | i + 1 => by
      intro a b hab
      rcases a with ⟨a, c⟩
      rcases b with ⟨b, d⟩
      let A := selectedPlaceData i a
      let B := selectedPlaceData i b
      have hparent : A.place = B.place :=
        splitUpperRationalPlace_parent_eq A.place B.place
          (distinguishedPlace i) (distinguishedCoordinate i)
          (distinguishedCoordinate_order i) A.coordinate_regular
          B.coordinate_regular c d hab
      have habIndex : a = b := solution i hparent
      subst b
      have hcd : c = d := by
        apply splitUpperRationalPlace_injective A.place
          (distinguishedPlace i) (distinguishedCoordinate i)
          (distinguishedCoordinate_order i) A.coordinate_regular
        exact hab
      exact Prod.ext rfl hcd
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalPlace_sourceStepRhs_order_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:10:47.070354+00:00
-- url     : https://prove2.me/submissions/1d1ec10d-54de-4f51-af1d-44d789b49280

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_trivialOnConstants
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepDistinguishedCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open IntermediateField
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
section SourceBasicRationalPlaces
open scoped BigOperators
attribute [local instance] sourceBasicRationalF256CharTwo
private theorem sourceBasicRationalPlace_order_X_of_pole
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k))
    (hX : 1 < P.valuation RatFunc.X) :
    P.order RatFunc.X = -1 := by
  classical
  have hXne : P.valuation RatFunc.X ≠ 0 :=
    P.valuation.ne_zero_iff.mpr RatFunc.X_ne_zero
  have hmultiple : ∀ f : RatFunc k, f ≠ 0 →
      ∃ n : ℤ, P.order f = n * P.order RatFunc.X := by
    intro f
    induction f using RatFunc.induction_on with
    | f p q hq =>
      intro hf
      have hp : p ≠ 0 := by
        intro hp
        subst p
        simp at hf
      refine ⟨(p.natDegree : ℤ) - (q.natDegree : ℤ), ?_⟩
      unfold GlobalPlace.order
      rw [map_div₀, ← RatFunc.coePolynomial_eq_algebraMap,
        ← RatFunc.coePolynomial_eq_algebraMap,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          k (v := P.valuation) hX hp,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          k (v := P.valuation) hX hq,
        WithZero.log_div (pow_ne_zero _ hXne) (pow_ne_zero _ hXne)]
      simp only [WithZero.log_pow, nsmul_eq_mul]
      ring
  have hu : P.uniformizer ≠ 0 := by
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  obtain ⟨n, hn⟩ := hmultiple P.uniformizer hu
  rw [P.order_uniformizer] at hn
  have hunit : P.order RatFunc.X = 1 ∨ P.order RatFunc.X = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (by
      simpa only [mul_comm] using hn.symm)
  have hpositive : 0 < WithZero.log (P.valuation RatFunc.X) := by
    simpa only [WithZero.log_one] using
      (WithZero.log_lt_log one_ne_zero hXne).mpr hX
  unfold GlobalPlace.order at hunit ⊢
  omega
private theorem sourceBasicRationalPlace_order_X_of_zero
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k))
    (hX : P.valuation RatFunc.X < 1) :
    P.order RatFunc.X = 1 := by
  let e := InverseAffinePlace.rationalInvolution k
  let Q := GlobalPlace.comapAlgEquiv e P
  have hQ : 1 < Q.valuation RatFunc.X := by
    change 1 < P.valuation (e RatFunc.X)
    rw [InverseAffinePlace.rationalInvolution_X, P.valuation.map_inv]
    exact (one_lt_inv₀ (pos_iff_ne_zero.mpr
      (P.valuation.ne_zero_iff.mpr RatFunc.X_ne_zero))).mpr hX
  have h := sourceBasicRationalPlace_order_X_of_pole Q hQ
  change (GlobalPlace.comapAlgEquiv e P).order RatFunc.X = -1 at h
  rw [GlobalPlace.comapAlgEquiv_order,
    InverseAffinePlace.rationalInvolution_X, P.order_inv] at h
  omega
private theorem sourceBasicRationalPlace_order_X_sub_constant_of_zero
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k)) (a : k)
    (hX : P.valuation (RatFunc.X - algebraMap k (RatFunc k) a) < 1) :
    P.order (RatFunc.X - algebraMap k (RatFunc k) a) = 1 := by
  let e : RatFunc k ≃ₐ[k] RatFunc k :=
    IsFractionRing.algEquivOfAlgEquiv (Polynomial.algEquivAevalXAddC (-a))
  have he : e RatFunc.X = RatFunc.X - algebraMap k (RatFunc k) a := by
    change IsFractionRing.algEquivOfAlgEquiv
      (Polynomial.algEquivAevalXAddC (-a))
      (algebraMap k[X] (RatFunc k) Polynomial.X) = _
    rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    simp [Polynomial.algEquivAevalXAddC_apply, sub_eq_add_neg]
  let Q := GlobalPlace.comapAlgEquiv e P
  have hQ : Q.valuation RatFunc.X < 1 := by
    change P.valuation (e RatFunc.X) < 1
    rwa [he]
  have h := sourceBasicRationalPlace_order_X_of_zero Q hQ
  change (GlobalPlace.comapAlgEquiv e P).order RatFunc.X = 1 at h
  simpa only [GlobalPlace.comapAlgEquiv_order, he] using h
private theorem sourceBasicRationalPlace_order_product
    {k ι : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k)) (s : Finset ι) (a : ι → k)
    (ha : Function.Injective a) (hX : P.valuation RatFunc.X ≤ 1) :
    P.order (∏ j ∈ s, (RatFunc.X - algebraMap k (RatFunc k) (a j))) = 0 ∨
    P.order (∏ j ∈ s, (RatFunc.X - algebraMap k (RatFunc k) (a j))) = 1 := by
  classical
  let f : ι → RatFunc k := fun j => RatFunc.X - algebraMap k (RatFunc k) (a j)
  have hle (j : ι) : P.valuation (f j) ≤ 1 := by
    apply (P.valuation.map_sub _ _).trans
    apply max_le hX
    by_cases hj : a j = 0
    · simp [hj]
    · exact le_of_eq ((GlobalPlace.trivialOnConstants P).eq_one _ hj)
  by_cases hsmall : ∃ j ∈ s, P.valuation (f j) < 1
  · obtain ⟨j, hj, hjlt⟩ := hsmall
    have hother (b : ι) (_hb : b ∈ s) (h : b ≠ j) : P.valuation (f b) = 1 := by
      have hab : a j - a b ≠ 0 := sub_ne_zero.mpr (fun he => h (ha he.symm))
      have hc : P.valuation (algebraMap k (RatFunc k) (a j - a b)) = 1 :=
        (GlobalPlace.trivialOnConstants P).eq_one _ hab
      have heq : f b = f j + algebraMap k (RatFunc k) (a j - a b) := by
        simp only [f, map_sub]
        ring
      rw [heq, P.valuation.map_add_eq_of_lt_right (hjlt.trans_eq hc.symm), hc]
    have hv : P.valuation (∏ b ∈ s, f b) = P.valuation (f j) := by
      rw [map_prod]
      exact Finset.prod_eq_single_of_mem j hj hother
    right
    change -WithZero.log (P.valuation (∏ b ∈ s, f b)) = 1
    rw [hv]
    exact sourceBasicRationalPlace_order_X_sub_constant_of_zero P (a j) hjlt
  · left
    have hone (j : ι) (hj : j ∈ s) : P.valuation (f j) = 1 :=
      le_antisymm (hle j) (not_lt.mp (fun h => hsmall ⟨j, hj, h⟩))
    change -WithZero.log (P.valuation (∏ b ∈ s, f b)) = 0
    rw [map_prod, Finset.prod_eq_one hone, WithZero.log_one, neg_zero]
private theorem sourceBasicRational_f16_factorization :
    (RatFunc.X : RatFunc F256) ^ 16 + RatFunc.X =
      ∏ a : F16, (RatFunc.X - algebraMap F256 (RatFunc F256) (f16Embedding a)) := by
  classical
  have hroots : (Polynomial.X ^ 16 - Polynomial.X : F16[X]).roots = Finset.univ.val := by
    simpa only [f16_card] using (FiniteField.roots_X_pow_card_sub_X F16)
  have hmonic : (Polynomial.X ^ 16 - Polynomial.X : F16[X]).Monic := by
    apply (Polynomial.monic_X_pow 16).sub_of_left
    simp only [Polynomial.degree_X, Polynomial.degree_X_pow]
    norm_num
  have hcard : (Polynomial.X ^ 16 - Polynomial.X : F16[X]).roots.card =
      (Polynomial.X ^ 16 - Polynomial.X : F16[X]).natDegree := by
    rw [hroots, Finset.card_val, Finset.card_univ, f16_card,
      FiniteField.X_pow_card_sub_X_natDegree_eq F16 (by norm_num)]
  have hp := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [hroots] at hp
  change (∏ a : F16, (Polynomial.X - Polynomial.C a)) =
    (Polynomial.X ^ 16 - Polynomial.X : F16[X]) at hp
  have he := congrArg (Polynomial.eval₂RingHom
    ((algebraMap F256 (RatFunc F256)).comp f16Embedding.toRingHom) RatFunc.X) hp.symm
  simp only [map_sub, map_pow, map_prod, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.comp_apply,
    sub_eq_add_neg, CharTwo.neg_eq] at he ⊢
  exact he
end SourceBasicRationalPlaces
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open IntermediateField
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open scoped BigOperators
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalF256CharTwo
attribute [local instance] sourceBasicRationalF256CharTwo
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 (RatFunc F256)) :
    P.order (sourceStepRhs RatFunc.X) = -1 ∨
      0 ≤ P.order (sourceStepRhs RatFunc.X) := by
  classical
  by_cases hf : sourceStepRhs (RatFunc.X : RatFunc F256) = 0
  · right
    simp [hf, GlobalPlace.order]
  have hXne : (RatFunc.X : RatFunc F256) ≠ 0 := RatFunc.X_ne_zero
  have hdenne : (RatFunc.X : RatFunc F256) ^ 15 + 1 ≠ 0 := by
    intro hzero
    apply hf
    simp [sourceStepRhs, hzero]
  rcases lt_trichotomy (P.valuation RatFunc.X) 1 with hlt | heq | hgt
  · right
    apply (P.regularAt_iff_order_nonnegative hf).mp
    have hpow : P.valuation (RatFunc.X ^ 15) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ zero_le hlt (by norm_num)
    have hden : P.valuation (RatFunc.X ^ 15 + 1) = 1 := by
      rw [P.valuation.map_add_eq_of_lt_right (hpow.trans_eq (map_one _).symm), map_one]
    change P.valuation (RatFunc.X ^ 16 / (RatFunc.X ^ 15 + 1)) ≤ 1
    rw [map_div₀, hden, div_one, map_pow]
    exact pow_le_one₀ zero_le hlt.le
  · have hXorder : P.order RatFunc.X = 0 := by
      simp [GlobalPlace.order, heq]
    have hprod := sourceBasicRationalPlace_order_product P Finset.univ
      f16Embedding f16Embedding.injective heq.le
    rw [← sourceBasicRational_f16_factorization] at hprod
    have hfactor : (RatFunc.X : RatFunc F256) ^ 16 + RatFunc.X =
        RatFunc.X * (RatFunc.X ^ 15 + 1) := by ring
    rw [hfactor, P.order_mul hXne hdenne, hXorder, zero_add] at hprod
    have hRhs : P.order (sourceStepRhs RatFunc.X) =
        -P.order (RatFunc.X ^ 15 + 1) := by
      rw [sourceStepRhs, div_eq_mul_inv,
        P.order_mul (pow_ne_zero 16 hXne) (inv_ne_zero hdenne), P.order_inv]
      have hnum : P.order (RatFunc.X ^ 16) = 0 := by
        simp [GlobalPlace.order, map_pow, heq]
      rw [hnum, zero_add]
    rcases hprod with hzero | hone
    · right
      simp [hRhs, hzero]
    · left
      rw [hRhs, hone]
  · left
    exact sourceStepRhs_order P RatFunc.X
      (sourceBasicRationalPlace_order_X_of_pole P hgt)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityRamificationIndex_sixteen_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:13:31.356236+00:00
-- url     : https://prove2.me/submissions/7e6f7c79-e638-4e80-983a-eb3ada460cb8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisSeedCoordinate_pow_sixteen_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceGaloisWFieldGenerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPlaceOfPrime_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPrime_nonempty
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_pos
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceGaloisWFieldGenerator
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivRatFunc_X
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepDistinguishedCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
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
private theorem sourceGaloisWRamification_sourceGaloisSeedCoordinate_ne_zero (m : ℕ) :
    sourceGaloisSeedCoordinate m ≠ 0 := by
  have h := (sourceGaloisSeedRatFuncToClosure m).injective.ne RatFunc.X_ne_zero
  simp only [map_zero] at h
  exact h
private theorem sourceGaloisWRamification_sourceGaloisWClosureGenerator_ne_zero (m : ℕ) :
    (sourceGaloisWClosureGenerator m : sourceGaloisWRamification_E m) ≠ 0 := by
  have hw : galoisBaseW ≠ 0 := by
    intro hzero
    apply sourceGaloisBaseW_transcendental
    rw [hzero]
    exact isAlgebraic_zero
  change sourceGaloisSeedRatFuncToClosure m galoisBaseW ≠ 0
  have h := (sourceGaloisSeedRatFuncToClosure m).injective.ne hw
  simp only [map_zero] at h
  exact h
private theorem sourceGaloisWRamification_sourceGaloisW_order_pow (m n : ℕ)
    (P : GlobalPlace F256 (sourceGaloisWRamification_E m)) (x : sourceGaloisWRamification_E m) :
    P.order (x ^ n) = (n : ℤ) * P.order x := by
  unfold GlobalPlace.order
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring
private theorem sourceGaloisWRamification_sourceGaloisW_valuation_eq_exp_neg_order (m : ℕ)
    (P : GlobalPlace F256 (sourceGaloisWRamification_E m)) (x : sourceGaloisWRamification_E m) (hx : x ≠ 0) :
    P.valuation x = WithZero.exp (-P.order x) := by
  unfold GlobalPlace.order
  rw [neg_neg]
  exact (WithZero.exp_log (P.valuation.ne_zero_iff.mpr hx)).symm
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    16 ∣ sourceGaloisWInfinityRamificationIndex m := by
  let P : SourceGaloisWInfinityPrime m :=
    Classical.choice (sourceGaloisWInfinityPrime_nonempty m)
  let Q : GlobalPlace F256 (sourceGaloisWRamification_E m) := sourceGaloisWInfinityPlaceOfPrime m P
  let x : sourceGaloisWRamification_E m := sourceGaloisSeedCoordinate m
  let w : sourceGaloisWRamification_E m := sourceGaloisWClosureGenerator m
  have hx : x ≠ 0 := by
    simpa only [x] using sourceGaloisWRamification_sourceGaloisSeedCoordinate_ne_zero m
  have hw : w ≠ 0 := by
    simpa only [w] using sourceGaloisWRamification_sourceGaloisWClosureGenerator_ne_zero m
  have hrelation : x ^ 16 + x = w := by
    simpa only [x, w] using sourceGaloisSeedCoordinate_pow_sixteen_add m
  have hworder : Q.order w =
      -(sourceGaloisWInfinityRamificationIndex m : ℤ) := by
    simpa only [Q, w] using
      sourceGaloisWInfinityPlaceOfPrime_order_generator m P
  have hxorder_neg : Q.order x < 0 := by
    by_contra hnot
    have hxorder_nonneg : 0 ≤ Q.order x := le_of_not_gt hnot
    have hxregular : GlobalPlace.RegularAt Q x :=
      (Q.regularAt_iff_order_nonnegative hx).mpr hxorder_nonneg
    have hxmem : x ∈ Q.valuationRing :=
      (Q.regularAt_iff_mem_valuationRing x).mp hxregular
    have hxpowmem : x ^ 16 ∈ Q.valuationRing :=
      Q.valuationRing.toSubring.pow_mem hxmem 16
    have hwmem : w ∈ Q.valuationRing := by
      rw [← hrelation]
      exact Q.valuationRing.add_mem _ _ hxpowmem hxmem
    have hwregular : GlobalPlace.RegularAt Q w :=
      (Q.regularAt_iff_mem_valuationRing w).mpr hwmem
    have hworder_nonneg : 0 ≤ Q.order w :=
      (Q.regularAt_iff_order_nonnegative hw).mp hwregular
    have hpositive := sourceGaloisWInfinityRamificationIndex_pos m
    omega
  have hxpow_order : Q.order (x ^ 16) = 16 * Q.order x := by
    simpa only [Nat.cast_ofNat] using sourceGaloisWRamification_sourceGaloisW_order_pow m 16 Q x
  have hxvalue : Q.valuation x = WithZero.exp (-Q.order x) :=
    sourceGaloisWRamification_sourceGaloisW_valuation_eq_exp_neg_order m Q x hx
  have hxpowvalue : Q.valuation (x ^ 16) =
      WithZero.exp (-(16 * Q.order x)) := by
    rw [sourceGaloisWRamification_sourceGaloisW_valuation_eq_exp_neg_order m Q (x ^ 16)
      (pow_ne_zero 16 hx), hxpow_order]
  have hvalue_lt : Q.valuation x < Q.valuation (x ^ 16) := by
    rw [hxvalue, hxpowvalue]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hsumorder : Q.order (x ^ 16 + x) = 16 * Q.order x := by
    calc
      Q.order (x ^ 16 + x) = Q.order (x ^ 16) := by
        unfold GlobalPlace.order
        rw [Q.valuation.map_add_eq_of_lt_left hvalue_lt]
      _ = 16 * Q.order x := hxpow_order
  rw [hrelation, hworder] at hsumorder
  let n : ℕ := Int.natAbs (Q.order x)
  have hn : (n : ℤ) = -Q.order x := by
    dsimp [n]
    rw [Int.natCast_natAbs, abs_of_neg hxorder_neg]
  refine ⟨n, ?_⟩
  have hcast : (sourceGaloisWInfinityRamificationIndex m : ℤ) =
      16 * (n : ℤ) := by
    calc
      (sourceGaloisWInfinityRamificationIndex m : ℤ) =
          -(16 * Q.order x) := by omega
      _ = 16 * (-Q.order x) := by ring
      _ = 16 * (n : ℤ) := by rw [← hn]
  exact_mod_cast hcast
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

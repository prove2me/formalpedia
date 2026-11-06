-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeed_inertiaDeg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:35:53.368434+00:00
-- url     : https://prove2.me/submissions/6977e972-38d7-43e2-a6a5-b1a72258b53b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
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
attribute [local instance 2000] sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceSeedBaseValuationRingSMul
attribute [local instance 2000] sourceSeedBaseValuationRingModule
attribute [local instance] sourceSeedBaseScalarTower
attribute [local instance] sourceSeedIntegralClosureTorsionFree
attribute [local instance] sourceSeedIntegralClosureFinite
attribute [local instance] sourceSeedIntegralClosureIsFractionRing
attribute [local instance] sourceSeedIntegralClosureIsDedekind
private theorem sourceSeed_ramificationIdx_mul_inertiaDeg_eq_one
    (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdx' P.1 *
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg' P.1 = 1 := by
  let O := SourceSeedBaseValuationRing
  let C := SourceSeedIntegralClosure m
  let K := GaloisBaseField
  let L := SourceField m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let s := IsDedekindDomain.primesOverFinset p C
  let f : Ideal C → ℕ := fun Q => p.ramificationIdx' Q * p.inertiaDeg' Q
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hPmem : P.1 ∈ s :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 C).2 P.2
  have hpositive : ∀ Q ∈ s, 0 < f Q := by
    intro Q hQ
    have hQdata := (IsDedekindDomain.mem_primesOverFinset_iff hp0 C).1 hQ
    letI : Q.IsPrime := hQdata.1
    letI : Q.LiesOver p := hQdata.2
    exact Nat.mul_pos
      (Nat.pos_of_ne_zero
        (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q hp0))
      (Nat.pos_of_ne_zero (Ideal.inertiaDeg_ne_zero p Q))
  have hrest : (s.erase P.1).card ≤ ∑ Q ∈ s.erase P.1, f Q := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun Q hQ =>
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (hpositive Q (Finset.mem_of_mem_erase hQ)))
  have hsum : ∑ Q ∈ s, f Q = Module.finrank K L :=
    Ideal.sum_ramification_inertia C K L hp0
  have hcard : s.card = Module.finrank K L := by
    calc
      s.card = (p.primesOver C).ncard := by
        rw [← IsDedekindDomain.coe_primesOverFinset hp0 C,
          Set.ncard_coe_finset]
      _ = 240 * 16 ^ m := sourceSeed_primesOver_ncard m
      _ = Module.finrank K L := (sourceSeed_fixedBase_finrank m).symm
  have hbound : f P.1 + (s.erase P.1).card ≤ Module.finrank K L := by
    calc
      f P.1 + (s.erase P.1).card ≤
          f P.1 + ∑ Q ∈ s.erase P.1, f Q :=
        Nat.add_le_add_left hrest _
      _ = ∑ Q ∈ s, f Q := Finset.add_sum_erase s f hPmem
      _ = Module.finrank K L := hsum
  have hcardErase : (s.erase P.1).card + 1 = Module.finrank K L := by
    calc
      (s.erase P.1).card + 1 = s.card := Finset.card_erase_add_one hPmem
      _ = Module.finrank K L := hcard
  have hfone : f P.1 = 1 := by
    have hfpos : 0 < f P.1 := hpositive P.1 hPmem
    omega
  exact hfone
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingSMul
attribute [local instance 2000] sourceSeedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingModule
attribute [local instance 2000] sourceSeedBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseScalarTower
attribute [local instance] sourceSeedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureTorsionFree
attribute [local instance] sourceSeedIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureFinite
attribute [local instance] sourceSeedIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsFractionRing
attribute [local instance] sourceSeedIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsDedekind
attribute [local instance] sourceSeedIntegralClosureIsDedekind
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg'
      P.1 = 1 := by
  apply Nat.eq_one_of_dvd_one
  refine ⟨(IsLocalRing.maximalIdeal
      SourceSeedBaseValuationRing).ramificationIdx' P.1, ?_⟩
  simpa only [Nat.mul_comm] using
    (sourceSeed_ramificationIdx_mul_inertiaDeg_eq_one m P).symm
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

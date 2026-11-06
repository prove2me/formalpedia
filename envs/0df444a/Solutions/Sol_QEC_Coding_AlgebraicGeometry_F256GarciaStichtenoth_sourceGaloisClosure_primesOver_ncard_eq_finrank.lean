-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosure_primesOver_ncard_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:37:22.969798+00:00
-- url     : https://prove2.me/submissions/2843ee30-c709-44f6-86cb-dce87a0dbc50

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Coset.Card
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureSplitting
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
open scoped Pointwise
attribute [local instance 3000] sourceGaloisClosureFieldBaseAlgebraPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseSMulPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseModulePinned
attribute [local instance 3000] sourceGaloisClosureGalFinite
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingModule
attribute [local instance] sourceGaloisClosureBaseScalarTower
attribute [local instance] sourceGaloisClosureSeedBaseScalarTower
attribute [local instance] sourceSeedIntegralClosureFractionTower
attribute [local instance] sourceGaloisClosureIntegralClosureFractionTower
attribute [local instance] sourceSeedIntegralClosureClosureAlgebra
attribute [local instance 2000] sourceSeedIntegralClosureClosureSMul
attribute [local instance 2000] sourceSeedIntegralClosureClosureModule
attribute [local instance] sourceGaloisClosureIntegralClosureScalarTower
attribute [local instance] sourceGaloisClosureIntegralOverSeedIntegral
attribute [local instance] sourceGaloisClosureIntegralOverSeedTorsionFree
attribute [local instance] sourceGaloisClosureIntegralClosureTorsionFree
attribute [local instance] sourceGaloisClosureIntegralClosureFinite
attribute [local instance] sourceGaloisClosureIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisClosureIntegralClosureIsDedekind
attribute [local instance] sourceGaloisClosureIntegralClosureAction
attribute [local instance 3000] sourceGaloisClosureIntegralClosureSMul
attribute [local instance 3000] sourceGaloisClosureIntegralClosureIdealAction
attribute [local instance 4000] sourceGaloisClosureIntegralClosureIdealMulAction
attribute [local instance] sourceGaloisClosureIntegralClosureActionCommutesWithBase
attribute [local instance] sourceGaloisClosureIntegralClosureIsGaloisGroup
attribute [local instance 3000] sourceSeedClosureFieldRangeAlgebra
attribute [local instance 3000] sourceSeedClosureFieldRangeSMul
attribute [local instance 3000] sourceSeedClosureFieldRangeModule
private theorem sourceGaloisClosureCosetContraction_surjective (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    Function.Surjective (sourceGaloisClosureCosetContraction m P) := by
  let p : Ideal SourceSeedBaseValuationRing :=
    IsLocalRing.maximalIdeal SourceSeedBaseValuationRing
  intro Q
  letI : Q.1.IsPrime := Q.2.1
  letI : Q.1.LiesOver p := Q.2.2
  letI : FaithfulSMul (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (sourceSeedIntegralClosureToClosure_injective m)
  obtain ⟨R⟩ := Q.1.nonempty_primesOver
    (S := SourceGaloisClosureIntegralClosure m)
  letI : R.1.IsPrime := R.2.1
  letI : R.1.LiesOver Q.1 := R.2.2
  letI : R.1.LiesOver p := Ideal.LiesOver.trans R.1 Q.1 p
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    p P.1 R.1 Gal((SourceGaloisClosureField m) / GaloisBaseField)
  refine ⟨Quotient.mk'' g⁻¹, ?_⟩
  change sourceGaloisClosureConjugateContraction m P g⁻¹ = Q
  apply Subtype.ext
  change ((g⁻¹)⁻¹ • P.1).under (SourceSeedIntegralClosure m) = Q.1
  rw [inv_inv, hg]
  exact R.2.2.over.symm
private theorem sourceGaloisClosureCoset_card (m : ℕ) :
    Nat.card (Gal((SourceGaloisClosureField m) / GaloisBaseField) ⧸
      sourceSeedClosureFixingSubgroup m) = 240 * 16 ^ m := by
  letI : Module GaloisBaseField
      (LinearMap.range (sourceGaloisSeedToClosure m).toLinearMap) :=
    SMulMemClass.toModule
      (LinearMap.range (sourceGaloisSeedToClosure m).toLinearMap)
  let rangeLinearEquiv : sourceSeedClosureFieldRange m ≃ₗ[GaloisBaseField]
      LinearMap.range (sourceGaloisSeedToClosure m).toLinearMap :=
    { toFun := fun x : sourceSeedClosureFieldRange m =>
        (⟨x.1, x.2⟩ : LinearMap.range
          (sourceGaloisSeedToClosure m).toLinearMap)
      invFun := fun x : LinearMap.range
          (sourceGaloisSeedToClosure m).toLinearMap =>
        (⟨x.1, x.2⟩ : sourceSeedClosureFieldRange m)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  calc
    Nat.card (Gal((SourceGaloisClosureField m) / GaloisBaseField) ⧸
        sourceSeedClosureFixingSubgroup m) =
        (sourceSeedClosureFixingSubgroup m).index :=
      (sourceSeedClosureFixingSubgroup m).index_eq_card.symm
    _ = Module.finrank GaloisBaseField (sourceSeedClosureFieldRange m) :=
      (IntermediateField.finrank_eq_fixingSubgroup_index
        (SourceGaloisClosureField m) (sourceSeedClosureFieldRange m)).symm
    _ = Module.finrank GaloisBaseField
        (LinearMap.range (sourceGaloisSeedToClosure m).toLinearMap) :=
      rangeLinearEquiv.finrank_eq
    _ = Module.finrank GaloisBaseField (SourceField m) :=
      LinearMap.finrank_range_of_inj (sourceGaloisSeedToClosure m).injective
    _ = 240 * 16 ^ m := sourceSeed_fixedBase_finrank m
private theorem sourceGaloisClosureCosetContraction_bijective (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    Function.Bijective (sourceGaloisClosureCosetContraction m P) := by
  apply (Nat.bijective_iff_surjective_and_card _).2
  refine ⟨sourceGaloisClosureCosetContraction_surjective m P, ?_⟩
  calc
    Nat.card (Gal((SourceGaloisClosureField m) / GaloisBaseField) ⧸
        sourceSeedClosureFixingSubgroup m) = 240 * 16 ^ m :=
      sourceGaloisClosureCoset_card m
    _ = ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceSeedIntegralClosure m)).ncard :=
      (sourceSeed_primesOver_ncard m).symm
    _ = Nat.card
        ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
          (SourceSeedIntegralClosure m)) :=
      (Nat.card_coe_set_eq _).symm
private theorem sourceGaloisClosurePrime_stabilizer_le_fixingSubgroup (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    MulAction.stabilizer
        Gal((SourceGaloisClosureField m) / GaloisBaseField) P.1 ≤
      sourceSeedClosureFixingSubgroup m := by
  intro d hd
  have hmap :
      sourceGaloisClosureCosetContraction m P (Quotient.mk'' d⁻¹) =
        sourceGaloisClosureCosetContraction m P (Quotient.mk'' 1) := by
    apply Subtype.ext
    change ((d⁻¹)⁻¹ • P.1).under (SourceSeedIntegralClosure m) =
      ((1 : Gal((SourceGaloisClosureField m) / GaloisBaseField))⁻¹ • P.1).under
        (SourceSeedIntegralClosure m)
    rw [inv_inv, inv_one, one_smul, MulAction.mem_stabilizer_iff.mp hd]
  have hquot := (sourceGaloisClosureCosetContraction_bijective m P).1 hmap
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hquot)
  simpa using hrel
private theorem sourceGaloisClosurePrime_stabilizer_conj_mem_fixingSubgroup
    (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m))
    {d : Gal((SourceGaloisClosureField m) / GaloisBaseField)}
    (hd : d ∈ MulAction.stabilizer
      Gal((SourceGaloisClosureField m) / GaloisBaseField) P.1)
    (g : Gal((SourceGaloisClosureField m) / GaloisBaseField)) :
    g⁻¹ * d * g ∈ sourceSeedClosureFixingSubgroup m := by
  let Q : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m) :=
    ⟨g⁻¹ • P.1, P.2.1.smul g⁻¹, P.2.2.smul g⁻¹⟩
  apply sourceGaloisClosurePrime_stabilizer_le_fixingSubgroup m Q
  rw [MulAction.mem_stabilizer_iff]
  change (g⁻¹ * d * g) • (g⁻¹ • P.1) = g⁻¹ • P.1
  simp only [mul_smul, smul_inv_smul,
    MulAction.mem_stabilizer_iff.mp hd]
private theorem sourceGaloisClosurePrime_stabilizer_fixes_seedEmbedding
    (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m))
    {d : Gal((SourceGaloisClosureField m) / GaloisBaseField)}
    (hd : d ∈ MulAction.stabilizer
      Gal((SourceGaloisClosureField m) / GaloisBaseField) P.1)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (x : SourceField m) :
    d (f x) = f x := by
  let g : Gal((SourceGaloisClosureField m) / GaloisBaseField) :=
    AlgEquiv.ofBijective (f.liftNormal (SourceGaloisClosureField m))
      (AlgHom.normal_bijective GaloisBaseField
        (SourceGaloisClosureField m) (SourceGaloisClosureField m)
          (f.liftNormal (SourceGaloisClosureField m)))
  have hg : g (sourceGaloisSeedToClosure m x) = f x := by
    change (f.liftNormal (SourceGaloisClosureField m))
        (algebraMap (SourceField m) (SourceGaloisClosureField m) x) =
      algebraMap (SourceGaloisClosureField m) (SourceGaloisClosureField m) (f x)
    exact AlgHom.liftNormal_commutes f (SourceGaloisClosureField m) x
  have hconj :=
    sourceGaloisClosurePrime_stabilizer_conj_mem_fixingSubgroup m P hd g
  rw [IntermediateField.mem_fixingSubgroup_iff] at hconj
  have hseed := hconj (sourceGaloisSeedToClosure m x) ⟨x, rfl⟩
  have happlied := congrArg (fun z : SourceGaloisClosureField m => g z) hseed
  simpa only [AlgEquiv.mul_apply, AlgEquiv.aut_inv,
    AlgEquiv.apply_symm_apply, hg] using happlied
private theorem sourceGaloisClosurePrime_stabilizer_eq_bot (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    MulAction.stabilizer
        Gal((SourceGaloisClosureField m) / GaloisBaseField) P.1 = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro d hd
  have hnormalTop :
      IntermediateField.normalClosure GaloisBaseField (SourceField m)
          (SourceGaloisClosureField m) = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (inferInstance : IsNormalClosure GaloisBaseField (SourceField m)
        (SourceGaloisClosureField m))).2
  have hle :
      IntermediateField.normalClosure GaloisBaseField (SourceField m)
          (SourceGaloisClosureField m) ≤
        FixedBy.intermediateField GaloisBaseField (SourceGaloisClosureField m) d := by
    rw [normalClosure_le_iff]
    intro f z hz
    rw [FixedBy.intermediateField_mem_iff]
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hz
    exact sourceGaloisClosurePrime_stabilizer_fixes_seedEmbedding m P hd f x
  apply AlgEquiv.ext
  intro z
  have hz : z ∈ FixedBy.intermediateField GaloisBaseField
      (SourceGaloisClosureField m) d := by
    apply hle
    rw [hnormalTop]
    exact IntermediateField.mem_top
  rw [FixedBy.intermediateField_mem_iff] at hz
  exact hz
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open scoped Pointwise
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureFieldBaseAlgebraPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseAlgebraPinned
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureFieldBaseSMulPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseSMulPinned
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureFieldBaseModulePinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseModulePinned
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureGalFinite
attribute [local instance 3000] sourceGaloisClosureGalFinite
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingBaseModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseValuationRingModule
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseScalarTower
attribute [local instance] sourceGaloisClosureBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseScalarTower
attribute [local instance] sourceGaloisClosureSeedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureFractionTower
attribute [local instance] sourceSeedIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureFractionTower
attribute [local instance] sourceGaloisClosureIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureClosureAlgebra
attribute [local instance] sourceSeedIntegralClosureClosureAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureClosureSMul
attribute [local instance 2000] sourceSeedIntegralClosureClosureSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureClosureModule
attribute [local instance 2000] sourceSeedIntegralClosureClosureModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureScalarTower
attribute [local instance] sourceGaloisClosureIntegralClosureScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralOverSeedIntegral
attribute [local instance] sourceGaloisClosureIntegralOverSeedIntegral
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralOverSeedTorsionFree
attribute [local instance] sourceGaloisClosureIntegralOverSeedTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureTorsionFree
attribute [local instance] sourceGaloisClosureIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureFinite
attribute [local instance] sourceGaloisClosureIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisClosureIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIsDedekind
attribute [local instance] sourceGaloisClosureIntegralClosureIsDedekind
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureAction
attribute [local instance] sourceGaloisClosureIntegralClosureAction
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureSMul
attribute [local instance 3000] sourceGaloisClosureIntegralClosureSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIdealAction
attribute [local instance 3000] sourceGaloisClosureIntegralClosureIdealAction
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIdealMulAction
attribute [local instance 4000] sourceGaloisClosureIntegralClosureIdealMulAction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureActionCommutesWithBase
attribute [local instance] sourceGaloisClosureIntegralClosureActionCommutesWithBase
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIsGaloisGroup
attribute [local instance] sourceGaloisClosureIntegralClosureIsGaloisGroup
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedClosureFieldRangeAlgebra
attribute [local instance 3000] sourceSeedClosureFieldRangeAlgebra
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedClosureFieldRangeSMul
attribute [local instance 3000] sourceSeedClosureFieldRangeSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedClosureFieldRangeModule
attribute [local instance 3000] sourceSeedClosureFieldRangeModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)).ncard =
        Module.finrank GaloisBaseField (SourceGaloisClosureField m) := by
  let O := SourceSeedBaseValuationRing
  let C := SourceGaloisClosureIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / GaloisBaseField)
  letI : p.IsPrime := inferInstance
  letI : FaithfulSMul O C :=
    (faithfulSMul_iff_algebraMap_injective O C).2 (by
      intro a b hab
      apply ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing
      apply (algebraMap GaloisBaseField (SourceGaloisClosureField m)).injective
      exact congrArg (fun z : C => (z : SourceGaloisClosureField m)) hab)
  obtain ⟨P⟩ := (inferInstance : Nonempty (p.primesOver C))
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  have horbit : MulAction.orbit G P.1 = p.primesOver C :=
    Algebra.IsInvariant.orbit_eq_primesOver O C G p P.1
  calc
    (p.primesOver C).ncard = (MulAction.orbit G P.1).ncard :=
      congrArg Set.ncard horbit.symm
    _ = (MulAction.stabilizer G P.1).index :=
      (MulAction.index_stabilizer G P.1).symm
    _ = (⊥ : Subgroup G).index := by
      rw [sourceGaloisClosurePrime_stabilizer_eq_bot m P]
    _ = Nat.card G := Subgroup.index_bot
    _ = Module.finrank GaloisBaseField (SourceGaloisClosureField m) :=
      IsGalois.card_aut_eq_finrank GaloisBaseField (SourceGaloisClosureField m)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

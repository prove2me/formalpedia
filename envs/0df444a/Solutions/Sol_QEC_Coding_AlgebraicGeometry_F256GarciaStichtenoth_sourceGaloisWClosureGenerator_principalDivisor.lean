-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGenerator_principalDivisor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:24:29.51823+00:00
-- url     : https://prove2.me/submissions/8c6c378b-f219-4aeb-aed4-e9bfdd418ba8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibreDivisors
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGeneratorPoleDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGenerator_polarDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceGaloisWFieldGenerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureField_ratFunc_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGenerator_pow_fifteen
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityFibreDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWRelativeDegree_mul_fifteen
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroFibreDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroFibreDivisor_support
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroPlaceOfPrime_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_chartVariable_degree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_repackage
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityFibreDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroFibreDivisor_apply
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGeneratorPoleDivisor_apply
section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open IntermediateField
open scoped Polynomial RatFunc
noncomputable section
attribute [local instance] sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra
attribute [local instance] sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable
private theorem sourceGaloisWPrincipalDivisor_closurePlaceEquiv_symm_order (m : ℕ)
    (P : sourceGaloisWPrincipalDivisor_ClosurePlace m) (x : sourceGaloisWPrincipalDivisor_E m) :
    sourceGaloisWPrincipalDivisor_directClosureOrder m ((sourceGaloisWPrincipalDivisor_closurePlaceEquiv m).symm P) x =
      sourceGaloisWPrincipalDivisor_closureOrder m P x := by
  change -WithZero.log
      (@GlobalPlace.valuation F256 (sourceGaloisWPrincipalDivisor_E m) _ _ _
        (@AffinePlace.constantAlgebra F256 (sourceGaloisWPrincipalDivisor_E m) _ _
          (sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m))
        ((sourceGaloisWPrincipalDivisor_closurePlaceEquiv m).symm P) x) =
    -WithZero.log
      (@GlobalPlace.valuation F256 (sourceGaloisWPrincipalDivisor_E m) _ _ _
        (sourceGaloisClosureConstantAlgebra m) P x)
  rfl
private theorem sourceGaloisWPrincipalDivisor_polarDivisorOnClosure_apply_of_ne (m : ℕ) (x : sourceGaloisWPrincipalDivisor_E m)
    (P : sourceGaloisWPrincipalDivisor_ClosurePlace m) (hx : x ≠ 0) :
    sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m x P = max (-sourceGaloisWPrincipalDivisor_closureOrder m P x) 0 := by
  unfold sourceGaloisWPrincipalDivisor_polarDivisorOnClosure
  simp only [dif_neg hx, Finsupp.sup_apply, Finsupp.neg_apply,
    Finsupp.zero_apply, GlobalPlace.principalDivisor_apply,
    Units.val_mk0]
private theorem sourceGaloisWPrincipalDivisor_polarDivisorOnDirectClosure_apply_of_ne (m : ℕ) (x : sourceGaloisWPrincipalDivisor_E m)
    (P : sourceGaloisWPrincipalDivisor_DirectClosurePlace m) (hx : x ≠ 0) :
    sourceGaloisWPrincipalDivisor_polarDivisorOnDirectClosure m x P =
      max (-sourceGaloisWPrincipalDivisor_directClosureOrder m P x) 0 := by
  unfold sourceGaloisWPrincipalDivisor_polarDivisorOnDirectClosure GlobalPlace.polarDivisor
  simp only [dif_neg hx, Finsupp.sup_apply, Finsupp.neg_apply,
    Finsupp.zero_apply, GlobalPlace.principalDivisor_apply,
    Units.val_mk0]
private theorem sourceGaloisWPrincipalDivisor_transportedDirectPolarDivisor_eq (m : ℕ) (x : sourceGaloisWPrincipalDivisor_E m) :
    sourceGaloisWPrincipalDivisor_transportedDirectPolarDivisor m x =
      sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m x := by
  classical
  ext P
  by_cases hx : x = 0
  · subst x
    simp [sourceGaloisWPrincipalDivisor_transportedDirectPolarDivisor, sourceGaloisWPrincipalDivisor_polarDivisorOnDirectClosure,
      GlobalPlace.polarDivisor, sourceGaloisWPrincipalDivisor_polarDivisorOnClosure]
  · rw [sourceGaloisWPrincipalDivisor_transportedDirectPolarDivisor, Finsupp.equivMapDomain_apply,
      sourceGaloisWPrincipalDivisor_polarDivisorOnDirectClosure_apply_of_ne m x _ hx,
      sourceGaloisWPrincipalDivisor_polarDivisorOnClosure_apply_of_ne m x P hx,
      sourceGaloisWPrincipalDivisor_closurePlaceEquiv_symm_order m P x]
private theorem sourceGaloisWPrincipalDivisor_divisor_degree_equivMapDomain
    {α β : Type*} (e : α ≃ β) (weight : β → ℕ) (D : Divisor α) :
    Divisor.degree weight (Finsupp.equivMapDomain e D) =
      Divisor.degree (fun a => weight (e a)) D := by
  change (Finsupp.equivMapDomain e D).sum
      (fun b coefficient => coefficient * (weight b : ℤ)) =
    D.sum (fun a coefficient => coefficient * (weight (e a) : ℤ))
  rw [Finsupp.sum_equivMapDomain]
private theorem sourceGaloisWPrincipalDivisor_sourceGaloisClosure_chartVariable_polarDivisor_degree (m : ℕ) :
    Divisor.degree (sourceGaloisWPrincipalDivisor_closureResidueDegree m)
        (sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m
          (GlobalPlace.chartVariable (k := F256) (F := sourceGaloisWPrincipalDivisor_E m))) =
      (Module.finrank (RatFunc F256) (sourceGaloisWPrincipalDivisor_E m) : ℤ) := by
  let e := sourceGaloisWPrincipalDivisor_closurePlaceEquiv m
  let D := sourceGaloisWPrincipalDivisor_polarDivisorOnDirectClosure m
    (GlobalPlace.chartVariable (k := F256) (F := sourceGaloisWPrincipalDivisor_E m))
  rw [← sourceGaloisWPrincipalDivisor_transportedDirectPolarDivisor_eq m]
  change Divisor.degree (sourceGaloisWPrincipalDivisor_closureResidueDegree m)
    (Finsupp.equivMapDomain e D) = _
  calc
    Divisor.degree (sourceGaloisWPrincipalDivisor_closureResidueDegree m)
        (Finsupp.equivMapDomain e D) =
        Divisor.degree (fun P => sourceGaloisWPrincipalDivisor_closureResidueDegree m (e P)) D :=
      sourceGaloisWPrincipalDivisor_divisor_degree_equivMapDomain e (sourceGaloisWPrincipalDivisor_closureResidueDegree m) D
    _ = Divisor.degree (sourceGaloisWPrincipalDivisor_directClosureResidueDegree m) D := by
      congr 1
      funext P
      exact GlobalPlace.residueDegree_repackage
        (@AffinePlace.constantAlgebra F256 (sourceGaloisWPrincipalDivisor_E m) _ _
          (sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m))
        (sourceGaloisClosureConstantAlgebra m) P
    _ = (Module.finrank (RatFunc F256) (sourceGaloisWPrincipalDivisor_E m) : ℤ) := by
      dsimp only [D, sourceGaloisWPrincipalDivisor_polarDivisorOnDirectClosure,
        sourceGaloisWPrincipalDivisor_directClosureResidueDegree]
      exact GlobalPlace.polarDivisor_chartVariable_degree_eq_finrank
        (π := sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m)
        (ρ := sourceGaloisClosureRatFuncAlgebra m)
        (τ := sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower m)
        (φ := sourceGaloisClosureFunctionField m)
        (s := sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable m)
        (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
private theorem sourceGaloisWPrincipalDivisor_order_pow (m n : ℕ)
    (P : GlobalPlace F256 (sourceGaloisWPrincipalDivisor_E m)) (x : sourceGaloisWPrincipalDivisor_E m) :
    P.order (x ^ n) = (n : ℤ) * P.order x := by
  unfold GlobalPlace.order
  rw [(P.valuation).map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring
private theorem sourceGaloisWPrincipalDivisor_sourceGaloisWClosureGenerator_pow_fifteen_eq_chartVariable
    (m : ℕ) :
    ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m) ^ 15 =
      GlobalPlace.chartVariable (k := F256) (F := sourceGaloisWPrincipalDivisor_E m) := by
  rw [sourceGaloisWClosureGenerator_pow_fifteen]
  change algebraMap GaloisBaseField (sourceGaloisWPrincipalDivisor_E m)
      (AdjoinSimple.gen F256 galoisBaseZ) =
    sourceGaloisClosureRatFuncEmbedding m RatFunc.X
  change algebraMap GaloisBaseField (sourceGaloisWPrincipalDivisor_E m)
      (AdjoinSimple.gen F256 galoisBaseZ) =
    algebraMap GaloisBaseField (sourceGaloisWPrincipalDivisor_E m)
      (galoisBaseFieldEquivRatFunc RatFunc.X)
  have hX : galoisBaseFieldEquivRatFunc RatFunc.X =
      AdjoinSimple.gen F256 galoisBaseZ := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X
      galoisBaseZ galoisBaseZ_transcendental
  rw [hX]
private theorem sourceGaloisWPrincipalDivisor_sourceGaloisWClosureGenerator_polarDivisor_pow_fifteen
    (m : ℕ) :
    sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m
        (((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m) ^ 15) =
      15 • sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m) := by
  let w : sourceGaloisWPrincipalDivisor_E m :=
    (sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m)
  have hw : w ≠ 0 := sourceGaloisWClosureGenerator_ne_zero m
  have hw_pow : w ^ 15 ≠ 0 := pow_ne_zero 15 hw
  ext P
  change sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m (w ^ 15) P =
    (15 • sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m w) P
  simp only [sourceGaloisWPrincipalDivisor_polarDivisorOnClosure, dif_neg hw_pow, dif_neg hw,
    Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.zero_apply,
    GlobalPlace.principalDivisor_apply, Units.val_mk0,
    Finsupp.smul_apply, nsmul_eq_mul]
  rw [sourceGaloisWPrincipalDivisor_order_pow m 15 P w]
  by_cases horder : 0 ≤ -P.order w
  · rw [max_eq_left horder, max_eq_left]
    · ring
    · omega
  · rw [max_eq_right (le_of_not_ge horder), max_eq_right]
    · simp
    · omega
private theorem sourceGaloisWPrincipalDivisor_sourceGaloisWClosureGenerator_polarDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisWClosureGeneratorPoleDivisor m) =
      (sourceGaloisWRelativeDegree m : ℤ) := by
  let D := sourceGaloisWClosureGeneratorPoleDivisor m
  have hscaled :
      (15 : ℤ) * Divisor.degree GlobalPlace.residueDegree D =
        (15 : ℤ) * (sourceGaloisWRelativeDegree m : ℤ) := by
    calc
      (15 : ℤ) * Divisor.degree GlobalPlace.residueDegree D =
          Divisor.degree GlobalPlace.residueDegree (15 • D) := by
        symm
        have h := (Divisor.degreeHom GlobalPlace.residueDegree).map_nsmul 15 D
        simp only [nsmul_eq_mul] at h
        exact h
      _ = Divisor.degree GlobalPlace.residueDegree
          (sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m
            (((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m) ^
              15)) :=
        congrArg (Divisor.degree GlobalPlace.residueDegree)
          (sourceGaloisWPrincipalDivisor_sourceGaloisWClosureGenerator_polarDivisor_pow_fifteen m).symm
      _ = Divisor.degree GlobalPlace.residueDegree
          (sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m
            (GlobalPlace.chartVariable (k := F256) (F := sourceGaloisWPrincipalDivisor_E m))) := by
        rw [sourceGaloisWPrincipalDivisor_sourceGaloisWClosureGenerator_pow_fifteen_eq_chartVariable]
      _ = (Module.finrank (RatFunc F256) (sourceGaloisWPrincipalDivisor_E m) : ℤ) :=
        sourceGaloisWPrincipalDivisor_sourceGaloisClosure_chartVariable_polarDivisor_degree m
      _ = (15 : ℤ) * (sourceGaloisWRelativeDegree m : ℤ) := by
        rw [sourceGaloisClosureField_ratFunc_finrank]
        norm_cast
        simpa only [sourceGaloisClosureSelectedLength] using
          (sourceGaloisWRelativeDegree_mul_fifteen m).symm
  dsimp only [D, sourceGaloisWClosureGeneratorPoleDivisor] at hscaled ⊢
  omega
private theorem sourceGaloisWPrincipalDivisor_residueDegree_pos (m : ℕ) (P : GlobalPlace F256 (sourceGaloisWPrincipalDivisor_E m)) :
    0 < GlobalPlace.residueDegree (k := F256) (F := sourceGaloisWPrincipalDivisor_E m) P := by
  letI : Algebra F256 (GlobalPlace.residueField P) :=
    GlobalPlace.residueAlgebra P
  letI : FiniteDimensional F256 (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  rw [GlobalPlace.residueDegree_eq_finrank P]
  exact Module.finrank_pos
private theorem sourceGaloisWPrincipalDivisor_divisorDegree_mono (m : ℕ)
    {D R : Divisor (GlobalPlace F256 (sourceGaloisWPrincipalDivisor_E m))} (hDR : D ≤ R) :
    Divisor.degree GlobalPlace.residueDegree D ≤
      Divisor.degree GlobalPlace.residueDegree R := by
  have hnonnegative : Divisor.Nonnegative (R - D) := by
    intro P
    exact sub_nonneg.mpr (hDR P)
  have hdegree_nonnegative :
      0 ≤ Divisor.degree GlobalPlace.residueDegree (R - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (R - D) = R := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegree_nonnegative
private theorem sourceGaloisWPrincipalDivisor_divisorDegree_single (m : ℕ)
    (P : GlobalPlace F256 (sourceGaloisWPrincipalDivisor_E m)) (coefficient : ℤ) :
    Divisor.degree GlobalPlace.residueDegree
        (Finsupp.single P coefficient) =
      coefficient * (GlobalPlace.residueDegree P : ℤ) := by
  simp [Divisor.degree, Divisor.degreeHom]
private theorem sourceGaloisWPrincipalDivisor_divisor_eq_of_le_of_degree_eq (m : ℕ)
    {D R : Divisor (GlobalPlace F256 (sourceGaloisWPrincipalDivisor_E m))} (hDR : D ≤ R)
    (hdegree : Divisor.degree GlobalPlace.residueDegree D =
      Divisor.degree GlobalPlace.residueDegree R) :
    R = D := by
  classical
  apply Finsupp.ext
  intro P
  have hnonnegative : 0 ≤ R P - D P := sub_nonneg.mpr (hDR P)
  have hdegree_sub :
      Divisor.degree GlobalPlace.residueDegree (R - D) = 0 := by
    rw [Divisor.degree_sub, hdegree, sub_self]
  have hsingle_le : Finsupp.single P (R P - D P) ≤ R - D := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg (Ne.symm hQP)]
      exact sub_nonneg.mpr (hDR Q)
  have hsingle_degree_le := sourceGaloisWPrincipalDivisor_divisorDegree_mono m hsingle_le
  rw [sourceGaloisWPrincipalDivisor_divisorDegree_single, hdegree_sub] at hsingle_degree_le
  have hresidue : 0 < (GlobalPlace.residueDegree P : ℤ) := by
    exact_mod_cast sourceGaloisWPrincipalDivisor_residueDegree_pos m P
  have hcoefficient : R P - D P = 0 := by
    by_contra hne
    have hpositive : 0 < R P - D P := lt_of_le_of_ne hnonnegative
      (Ne.symm hne)
    exact (not_lt_of_ge hsingle_degree_le)
      (mul_pos hpositive hresidue)
  omega
private theorem sourceGaloisWPrincipalDivisor_principalDivisor_add_polarDivisor_nonnegative (m : ℕ) :
    Divisor.Nonnegative
      (GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
          (Units.mk0
            ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)
            (sourceGaloisWClosureGenerator_ne_zero m)) +
        sourceGaloisWClosureGeneratorPoleDivisor m) := by
  intro P
  have hw := sourceGaloisWClosureGenerator_ne_zero m
  simp only [Finsupp.add_apply, GlobalPlace.principalDivisor_apply,
    Units.val_mk0, sourceGaloisWClosureGeneratorPoleDivisor,
    sourceGaloisWPrincipalDivisor_polarDivisorOnClosure, dif_neg hw,
    Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.zero_apply]
  omega
private theorem sourceGaloisWPrincipalDivisor_zeroFibre_smul_le_principal_add_polar (m : ℕ) :
    sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m ≤
      GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
          (Units.mk0
            ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)
            (sourceGaloisWClosureGenerator_ne_zero m)) +
        sourceGaloisWClosureGeneratorPoleDivisor m := by
  classical
  intro Q
  letI : Decidable (Q ∈ Set.range (sourceGaloisWZeroPlaceOfPrime m)) :=
    Classical.propDecidable _
  by_cases hQ : Q ∈ Set.range (sourceGaloisWZeroPlaceOfPrime m)
  · rcases hQ with ⟨P, rfl⟩
    have hw := sourceGaloisWClosureGenerator_ne_zero m
    simp only [Finsupp.smul_apply, nsmul_eq_mul,
      sourceGaloisWZeroFibreDivisor_apply, mul_one, Finsupp.add_apply,
      GlobalPlace.principalDivisor_apply, Units.val_mk0,
      sourceGaloisWClosureGeneratorPoleDivisor, sourceGaloisWPrincipalDivisor_polarDivisorOnClosure,
      dif_neg hw, Finsupp.sup_apply,
      Finsupp.neg_apply, Finsupp.zero_apply]
    rw [sourceGaloisWZeroPlaceOfPrime_order_generator]
    have hnonnegative :
        0 ≤ (sourceGaloisWZeroRamificationIndex m : ℤ) := by positivity
    rw [max_eq_right (by omega), add_zero]
  · have hzero : sourceGaloisWZeroFibreDivisor m Q = 0 := by
      by_contra hne
      have hmem : Q ∈ ↑(sourceGaloisWZeroFibreDivisor m).support :=
        Divisor.mem_support_iff.mpr hne
      have hmemSet : Q ∈
          (↑(sourceGaloisWZeroFibreDivisor m).support : Set _) := by
        exact hmem
      rw [sourceGaloisWZeroFibreDivisor_support] at hmemSet
      exact hQ hmemSet
    rw [Finsupp.smul_apply, hzero, nsmul_zero]
    exact sourceGaloisWPrincipalDivisor_principalDivisor_add_polarDivisor_nonnegative m Q
private theorem sourceGaloisWPrincipalDivisor_principalDivisor_add_polarDivisor_eq_zeroFibre (m : ℕ) :
    GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
          (Units.mk0
            ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)
            (sourceGaloisWClosureGenerator_ne_zero m)) +
        sourceGaloisWClosureGeneratorPoleDivisor m =
      sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m := by
  apply sourceGaloisWPrincipalDivisor_divisor_eq_of_le_of_degree_eq m
    (sourceGaloisWPrincipalDivisor_zeroFibre_smul_le_principal_add_polar m)
  calc
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m) =
        (sourceGaloisWZeroRamificationIndex m : ℤ) *
          Divisor.degree GlobalPlace.residueDegree
            (sourceGaloisWZeroFibreDivisor m) := by
      simpa only [Divisor.degree, nsmul_eq_mul] using
        (Divisor.degreeHom GlobalPlace.residueDegree).map_nsmul
          (sourceGaloisWZeroRamificationIndex m) (sourceGaloisWZeroFibreDivisor m)
    _ = (sourceGaloisWRelativeDegree m : ℤ) :=
      sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree m
    _ = Divisor.degree GlobalPlace.residueDegree
        (GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
            (Units.mk0
              ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)
              (sourceGaloisWClosureGenerator_ne_zero m)) +
          sourceGaloisWClosureGeneratorPoleDivisor m) := by
      rw [Divisor.degree_add, GlobalPlace.principalDivisor_degree_zero,
        zero_add, sourceGaloisWPrincipalDivisor_sourceGaloisWClosureGenerator_polarDivisor_degree]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open IntermediateField
open scoped Polynomial RatFunc
noncomputable section
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra
attribute [local instance] sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable
attribute [local instance] sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
        (Units.mk0
          ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)
          (sourceGaloisWClosureGenerator_ne_zero m)) =
      sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m -
        sourceGaloisWInfinityRamificationIndex m •
          sourceGaloisWInfinityFibreDivisor m := by
  calc
    GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
        (Units.mk0
          ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)
          (sourceGaloisWClosureGenerator_ne_zero m)) =
        (GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
            (Units.mk0
              ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)
              (sourceGaloisWClosureGenerator_ne_zero m)) +
          sourceGaloisWClosureGeneratorPoleDivisor m) -
          sourceGaloisWClosureGeneratorPoleDivisor m := by
      abel
    _ = sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m -
        sourceGaloisWClosureGeneratorPoleDivisor m := by
      rw [sourceGaloisWPrincipalDivisor_principalDivisor_add_polarDivisor_eq_zeroFibre]
    _ = sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m -
        sourceGaloisWInfinityRamificationIndex m •
          sourceGaloisWInfinityFibreDivisor m := by
      rw [sourceGaloisWClosureGenerator_polarDivisor]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

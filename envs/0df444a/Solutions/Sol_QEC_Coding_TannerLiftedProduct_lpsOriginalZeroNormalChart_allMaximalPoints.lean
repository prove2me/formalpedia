-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalZeroNormalChart_allMaximalPoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:47:20.946219+00:00
-- url     : https://prove2.me/submissions/9d0cd01a-174d-4284-bb29-c76fbba18597

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPoleClearingAway
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroPointCoverage
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PolynomialMaximalPoints_complexPolynomialMaximal_exists_eval
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PolynomialMaximalPoints_finitePrimeAvoidance
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_interior_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_integral_iff_noInteriorPole
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_polynomial_clear_away
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFibre_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroCoverageDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroCoverageDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroCoverageDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroCoverageDictionary004
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (M : Ideal R) [M.IsMaximal] :
    ∃ x : Q, M = RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN (Sum.inl x)
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x)) := by
  classical
  let E (x : Q) : R →+* ℂ := lpsOriginalZeroNormalChartEvaluation N hpos hN (Sum.inl x)
    (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x)
  let C : Ideal P := M.comap (algebraMap P R)
  let : C.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  obtain ⟨α,hα⟩ := complexPolynomialMaximal_exists_eval C
  have hbase (p : P) : algebraMap P R p ∈ M ↔ p.eval α = 0 := hα p
  have hXmem : algebraMap P R (Polynomial.X - Polynomial.C α) ∈ M :=
    (hbase _).mpr (by simp)
  have hinj : Function.Injective (algebraMap P K) :=
    (algebraMap J K).injective.comp (IsFractionRing.injective P J)
  have hXne : algebraMap P R (Polynomial.X - Polynomial.C α) ≠ 0 := by
    intro hz
    have hval := congrArg Subtype.val hz
    change algebraMap P K (Polynomial.X - Polynomial.C α) = 0 at hval
    exact Polynomial.X_sub_C_ne_zero α (hinj (hval.trans (map_zero _).symm))
  have hMbot : M ≠ ⊥ := by intro hz; rw [hz,Ideal.mem_bot] at hXmem;exact hXne hXmem
  by_contra hcoverage
  push Not at hcoverage
  let Y : Set Q := {x | lpsOriginalFilledJ N (Sum.inl x) = α}
  have hY : Y.Finite := lpsOriginalJFibre_finite N hpos hN α
  let S : Set (Ideal R) := insert ⊥ ((fun x : Q => RingHom.ker (E x)) '' Y)
  have hS : S.Finite := (hY.image _).insert _
  have hprime : ∀ I ∈ S, I.IsPrime := by
    intro I hI
    obtain rfl | ⟨x,hx,rfl⟩ := hI
    · infer_instance
    · exact (lpsOriginalZeroEvaluation_ker_isMaximal N hpos hN (Sum.inl x)
        (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x)).isPrime
  have houtside : M ∉ S := by
    intro hM
    obtain hz | ⟨x,hx,hEq⟩ := hM
    · exact hMbot hz
    · exact hcoverage x hEq.symm
  obtain ⟨g,hg,havoid⟩ := finitePrimeAvoidance M S hS hprime houtside
  have hg0 : g ≠ 0 := by simpa only [Ideal.mem_bot] using havoid ⊥ (Set.mem_insert _ _)
  have hgv0 : g.val ≠ 0 := by intro hz;apply hg0;exact Subtype.ext hz
  have hgorder (x : Q) (hx : lpsOriginalFilledJ N (Sum.inl x) = α) :
      lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) g.val = 0 := by
    have hnot : E x g ≠ 0 := havoid (RingHom.ker (E x))
      (Set.mem_insert_of_mem _ ⟨x,hx,rfl⟩)
    have hle : lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) g.val ≤ 0 := by
      apply le_of_not_gt
      intro hp
      exact hnot ((lpsOriginalZeroEvaluation_eq_zero_iff_order_pos N hpos hN (Sum.inl x)
        (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) g).mpr hp)
    exact le_antisymm hle ((lpsOriginalField_integral_iff_noInteriorPole N hpos hN g.val).mp g.property x)
  have hinv (x : Q) (hx : lpsOriginalFilledJ N (Sum.inl x) = α) :
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) g.val⁻¹ := by
    rw [AddValuation.map_inv,hgorder x hx,neg_zero]
  obtain ⟨H,hHα,hHint⟩ := lpsOriginalField_polynomial_clear_away N hpos hN g.val⁻¹ α hinv
  let b : R := ⟨algebraMap P K H*g.val⁻¹,hHint⟩
  have hgb : g*b = algebraMap P R H := by
    apply Subtype.ext
    change g.val*(algebraMap P K H*g.val⁻¹) = algebraMap P K H
    calc
      _ = algebraMap P K H*(g.val*g.val⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hgv0,mul_one]
  have hHM : algebraMap P R H ∈ M := by rw [←hgb];exact M.mul_mem_right b hg
  exact hHα ((hbase H).mp hHM)
end QEC.Coding.TannerLiftedProduct

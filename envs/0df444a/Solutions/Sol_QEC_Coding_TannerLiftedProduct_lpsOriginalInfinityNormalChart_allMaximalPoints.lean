-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityNormalChart_allMaximalPoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:49:41.785908+00:00
-- url     : https://prove2.me/submissions/3a7503f6-5cf6-43fd-a0ea-99ac61d82c62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPoleClearingAway
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPointCoverage
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_reciprocal_polynomial_clear_away
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityCoordinate_fibre_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalPolynomialMap_injective
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
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityPointCoverageDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityPointCoverageDictionary002
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (M : Ideal R) [M.IsMaximal] :
    ∃ x : S, M = RingHom.ker
      (lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property) := by
  classical
  let E (x : S) : R →+* ℂ := lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property
  let β := lpsOriginalInfinityCoordinate N hpos hN
  let C : Ideal P := M.comap (algebraMap P R)
  let : C.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  obtain ⟨α,hα⟩ := complexPolynomialMaximal_exists_eval C
  have hbase (p : P) : algebraMap P R p ∈ M ↔ p.eval α = 0 := hα p
  have hXmem : algebraMap P R (Polynomial.X - Polynomial.C α) ∈ M :=
    (hbase _).mpr (by simp)
  have hinj : Function.Injective (algebraMap P K) :=
    lpsOriginalReciprocalPolynomialMap_injective N hpos
  have hXne : algebraMap P R (Polynomial.X - Polynomial.C α) ≠ 0 := by
    intro hz
    have hval := congrArg Subtype.val hz
    change algebraMap P K (Polynomial.X - Polynomial.C α) = 0 at hval
    exact Polynomial.X_sub_C_ne_zero α (hinj (hval.trans (map_zero _).symm))
  have hMbot : M ≠ ⊥ := by intro hz; rw [hz,Ideal.mem_bot] at hXmem;exact hXne hXmem
  by_contra hcoverage
  push Not at hcoverage
  let Y : Set S := {x | β x = α}
  have hY : Y.Finite := lpsOriginalInfinityCoordinate_fibre_finite N hpos hN α
  let I : Set (Ideal R) := insert ⊥ ((fun x : S => RingHom.ker (E x)) '' Y)
  have hI : I.Finite := (hY.image _).insert _
  have hprime : ∀ i ∈ I, i.IsPrime := by
    intro i hi
    obtain rfl | ⟨x,hx,rfl⟩ := hi
    · infer_instance
    · exact (lpsOriginalInfinityEvaluation_ker_isMaximal N hpos hN x.val x.property).isPrime
  have houtside : M ∉ I := by
    intro hM
    obtain hz | ⟨x,hx,hEq⟩ := hM
    · exact hMbot hz
    · exact hcoverage x hEq.symm
  obtain ⟨g,hg,havoid⟩ := finitePrimeAvoidance M I hI hprime houtside
  have hg0 : g ≠ 0 := by simpa only [Ideal.mem_bot] using havoid ⊥ (Set.mem_insert _ _)
  have hgv0 : g.val ≠ 0 := by intro hz;apply hg0;exact Subtype.ext hz
  have hgorder (x : S) (hx : β x = α) :
      lpsOriginalFieldLocalOrder N hN hpos x.val g.val = 0 := by
    have hnot : E x g ≠ 0 := havoid (RingHom.ker (E x))
      (Set.mem_insert_of_mem _ ⟨x,hx,rfl⟩)
    have hle : lpsOriginalFieldLocalOrder N hN hpos x.val g.val ≤ 0 := by
      apply le_of_not_gt
      intro hp
      exact hnot ((lpsOriginalInfinityEvaluation_eq_zero_iff_order_pos N hpos hN
        x.val x.property g).mpr hp)
    exact le_antisymm hle (lpsOriginalInfinityIntegral_order_nonnegative N hpos hN x.val x.property g)
  have hinv (x : S) (hx : β x = α) :
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val g.val⁻¹ := by
    rw [AddValuation.map_inv,hgorder x hx,neg_zero]
  obtain ⟨H,hHα,hHint⟩ := lpsOriginalField_reciprocal_polynomial_clear_away
    N hpos hN g.val⁻¹ α hinv
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

-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_and_forall_comp_and_kernelIdealSet_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/559b1873-9167-5cd7-8786-c41831f53708

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_and_forall_comp_and_kernelIdealSet_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map Affine.Point.some toAffine Affine.Point Affine.Point.neg_some baseChange evalEvalBC IsRationallyRepresented rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet kernelIdealSet exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp add_mem_rationalHomSet comp_mem_rationalHomSet"
p2m_open "WeierstrassCurve"

namespace KernelIdealAnnihilator

open Polynomial
open scoped Polynomial.Bivariate

universe u v

section NegClosure

variable {F : Type u} [Field F] (k : Type v) [Field k] [Algebra F k]

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k p x y =
      ((evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))) p := by
  rfl

theorem evalEvalBC_mul (p q : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k (p * q) x y =
      WeierstrassCurve.evalEvalBC k p x y * WeierstrassCurve.evalEvalBC k q x y := by
  simp only [evalEvalBC_eq, map_mul]

theorem evalEvalBC_sub (p q : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k (p - q) x y =
      WeierstrassCurve.evalEvalBC k p x y - WeierstrassCurve.evalEvalBC k q x y := by
  simp only [evalEvalBC_eq, map_sub]

theorem evalEvalBC_neg (p : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k (-p) x y = -WeierstrassCurve.evalEvalBC k p x y := by
  simp only [evalEvalBC_eq, map_neg]

theorem evalEvalBC_C_C (c : F) (x y : k) :
    WeierstrassCurve.evalEvalBC k (C (C c)) x y = algebraMap F k c := by
  simp [WeierstrassCurve.evalEvalBC, Polynomial.evalEval]

theorem some_congr_y {W : WeierstrassCurve.Affine k} {x y₁ y₂ : k} (h₁ : W.Nonsingular x y₁)
    (hy : y₁ = y₂) :
    ∃ h₂ : W.Nonsingular x y₂, WeierstrassCurve.Affine.Point.some x y₁ h₁ = .some x y₂ h₂ := by
  subst hy; exact ⟨h₁, rfl⟩

variable [DecidableEq k]

theorem isRationallyRepresented_neg (W₁ W₂ : WeierstrassCurve F)
    (α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point)
    (hα : WeierstrassCurve.IsRationallyRepresented k W₁ W₂ α) :
    WeierstrassCurve.IsRationallyRepresented k W₁ W₂ (-α) := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine ⟨nX, dX, -(nY * dX) - C (C W₂.a₁) * nX * dY - C (C W₂.a₃) * dX * dY, dY * dX, B, hB,
    fun x y h hx => ?_⟩
  obtain ⟨hdX, hdY, h', hαP⟩ := hrep x y h hx
  refine ⟨hdX, ?_, ?_⟩
  · rw [evalEvalBC_mul]; exact mul_ne_zero hdY hdX
  · have hneg : (-α) (.some x y h) = -(α (.some x y h)) := rfl
    rw [hneg, hαP, WeierstrassCurve.Affine.Point.neg_some]
    apply some_congr_y
    simp only [WeierstrassCurve.Affine.negY, evalEvalBC_sub, evalEvalBC_neg, evalEvalBC_mul,
      evalEvalBC_C_C]
    have ha₁ : (W₂.baseChange k).toAffine.a₁ = algebraMap F k W₂.a₁ := rfl
    have ha₃ : (W₂.baseChange k).toAffine.a₃ = algebraMap F k W₂.a₃ := rfl
    rw [ha₁, ha₃]
    field_simp

theorem neg_mem_rationalHomSet (W₁ W₂ : WeierstrassCurve F)
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) :
    -α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂ := by
  rcases hα with rfl | hα
  · rw [neg_zero]; exact WeierstrassCurve.zero_mem_rationalHomSet k W₁ W₂
  · exact Or.inr (isRationallyRepresented_neg k W₁ W₂ α hα)

theorem mem_rationalHomSet_of_mem_rationalEndSubring [IsAlgClosed k]
    (W : WeierstrassCurve F) [W.IsElliptic]
    {α : AddMonoid.End (W.baseChange k).toAffine.Point}
    (h : α ∈ WeierstrassCurve.rationalEndSubring k W) :
    (α : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      WeierstrassCurve.rationalHomSet k W W := by
  unfold WeierstrassCurve.rationalEndSubring at h
  induction h using Subring.closure_induction with
  | mem x hx => exact hx
  | zero => exact WeierstrassCurve.zero_mem_rationalHomSet k W W
  | one => exact WeierstrassCurve.id_mem_rationalHomSet k W
  | add x y _ _ hx hy => exact WeierstrassCurve.add_mem_rationalHomSet k W W hx hy
  | neg x _ hx => exact neg_mem_rationalHomSet k W W hx
  | mul x y _ _ hx hy => exact WeierstrassCurve.comp_mem_rationalHomSet k W W W hy hx

end NegClosure

section Card

variable {κ : Type} [Field κ] [DecidableEq κ]

theorem natCard_cast_ne_zero (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (H : AddSubgroup (X₀.baseChange κ).toAffine.Point)
    (hH : (H : Set (X₀.baseChange κ).toAffine.Point).Finite) :
    ((Nat.card H : ℕ) : κ) ≠ 0 := by
  haveI : Finite H := hH.to_subtype
  intro h0
  rw [CharP.cast_eq_zero_iff κ q'] at h0
  obtain ⟨Q, hQ⟩ := exists_prime_addOrderOf_dvd_card' (G := H) q' h0
  have hQ' : addOrderOf (Q : (X₀.baseChange κ).toAffine.Point) = q' := by
    rw [AddSubgroup.addOrderOf_coe, hQ]
  have hnsmul : q' • (Q : (X₀.baseChange κ).toAffine.Point) = 0 := by
    rw [← hQ']; exact addOrderOf_nsmul_eq_zero _
  have hzero : (Q : (X₀.baseChange κ).toAffine.Point) = 0 := hss _ hnsmul
  have h1 : addOrderOf (Q : (X₀.baseChange κ).toAffine.Point) = 1 := by
    rw [hzero, addOrderOf_zero]
  have hq1 : q' = 1 := hQ'.symm.trans h1
  exact (Fact.out : q'.Prime).one_lt.ne' hq1

end Card

end KernelIdealAnnihilator

end WeierstrassCurve

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (H : AddSubgroup (X₀.baseChange κ).toAffine.Point) (hH : (H : Set (X₀.baseChange κ).toAffine.Point).Finite) :
    ∃ (W : WeierstrassCurve κ) (_ : W.IsElliptic) (φ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
      (_ : φ ∈ WeierstrassCurve.rationalHomSet κ X₀ W),
      φ.ker = H ∧
      (∀ (W₃ : WeierstrassCurve κ) [W₃.IsElliptic] (α : (X₀.baseChange κ).toAffine.Point →+ (W₃.baseChange κ).toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet κ X₀ W₃ → (∀ P ∈ H, α P = 0) →
          ∃ β ∈ WeierstrassCurve.rationalHomSet κ W W₃, α = β.comp φ) ∧
      WeierstrassCurve.kernelIdealSet κ X₀ W φ =
        {α : ↥(WeierstrassCurve.rationalEndSubring κ X₀) | ∀ P ∈ H, (α : AddMonoid.End (X₀.baseChange κ).toAffine.Point) P = 0} := by

  have hcard : ((Nat.card H : ℕ) : κ) ≠ 0 :=
    WeierstrassCurve.KernelIdealAnnihilator.natCard_cast_ne_zero q' X₀ hss H hH

  obtain ⟨W, hW, φ, hφ, hφs, hker, huniv⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp X₀ H hcard
  haveI := hW
  refine ⟨W, hW, φ, hφ, hker, ?_, ?_⟩
  ·
    intro W₃ _ α hα hαH
    exact huniv W₃ α hα (fun P hP => (AddMonoidHom.mem_ker (f := α)).mpr (hαH P hP))
  ·
    ext a
    constructor
    ·
      rintro ⟨ρ, hρ, ha⟩ P hP
      have hφP : φ P = 0 := by
        rw [← AddMonoidHom.mem_ker (f := φ), hker]; exact hP
      show ((a : AddMonoid.End (X₀.baseChange κ).toAffine.Point) :
          (X₀.baseChange κ).toAffine.Point →+ (X₀.baseChange κ).toAffine.Point) P = 0
      rw [ha]
      show ρ (φ P) = 0
      rw [hφP, map_zero]
    ·
      intro ha
      have hmem : ((a : AddMonoid.End (X₀.baseChange κ).toAffine.Point) :
          (X₀.baseChange κ).toAffine.Point →+ (X₀.baseChange κ).toAffine.Point) ∈
            WeierstrassCurve.rationalHomSet κ X₀ X₀ :=
        WeierstrassCurve.KernelIdealAnnihilator.mem_rationalHomSet_of_mem_rationalEndSubring κ X₀ a.2
      have hkerle : H ≤ AddMonoidHom.ker ((a : AddMonoid.End (X₀.baseChange κ).toAffine.Point) :
          (X₀.baseChange κ).toAffine.Point →+ (X₀.baseChange κ).toAffine.Point) := by
        intro P hP
        rw [AddMonoidHom.mem_ker]
        exact ha P hP
      obtain ⟨β, hβ, hβeq⟩ := huniv X₀ _ hmem hkerle
      exact ⟨β, hβ, hβeq⟩

end S_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_and_forall_comp_and_kernelIdealSet_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_and_forall_comp_and_kernelIdealSet_eq (solution)

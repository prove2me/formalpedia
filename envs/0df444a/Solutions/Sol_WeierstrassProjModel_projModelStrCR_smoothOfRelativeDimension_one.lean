-- Prove2me | solution 1 for WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2eb160ad-4331-53cc-b88f-43cbb76ee511

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Theorems.Thm_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace ProjWeierstrassDehomog

open MvPolynomial

section PointDictionary

variable {R : Type*} [CommRing R]

theorem X_eq_zero_and_Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R]
    {V : WeierstrassCurve.Projective R} {P : Fin 3 → R}
    (hP : eval P V.polynomial = 0) (hPz : P 2 = 0) (hP0 : P ≠ 0) :
    P 0 = 0 ∧ P 1 ≠ 0 := by
  have hx : P 0 = 0 := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero (W' := V) hP hPz
  refine ⟨hx, fun hy => hP0 ?_⟩
  funext i
  fin_cases i
  · exact hx
  · exact hy
  · exact hPz

end PointDictionary

variable {R : Type*} [CommRing R]

theorem eval_polynomialZ_of_Z_eq_zero (V : WeierstrassCurve.Projective R) (P : Fin 3 → R)
    (hPz : P 2 = 0) :
    eval P V.polynomialZ = P 1 ^ 2 + V.a₁ * P 0 * P 1 - V.a₂ * P 0 ^ 2 := by
  rw [WeierstrassCurve.Projective.eval_polynomialZ, hPz]
  ring

theorem nonsingular_of_equation_of_Z_eq_zero [NoZeroDivisors R]
    {V : WeierstrassCurve.Projective R} {P : Fin 3 → R}
    (hP : eval P V.polynomial = 0) (hPz : P 2 = 0) (hP0 : P ≠ 0) :
    V.Nonsingular P := by
  obtain ⟨hx, hy⟩ := X_eq_zero_and_Y_ne_zero_of_Z_eq_zero hP hPz hP0
  have hZ : eval P V.polynomialZ = P 1 ^ 2 := by
    rw [eval_polynomialZ_of_Z_eq_zero V P hPz, hx]
    ring
  refine ⟨hP, Or.inr (Or.inr ?_)⟩
  rw [hZ]
  exact pow_ne_zero 2 hy

theorem nonsingular_of_equation_of_forall_affine_nonsingular {F : Type*} [Field F]
    {V : WeierstrassCurve.Projective F}
    (h : ∀ a b : F, V.toAffine.Equation a b → V.toAffine.Nonsingular a b)
    {P : Fin 3 → F} (hP : eval P V.polynomial = 0) (hP0 : P ≠ 0) :
    V.Nonsingular P := by
  by_cases hPz : P 2 = 0
  · exact nonsingular_of_equation_of_Z_eq_zero hP hPz hP0
  · have hE : V.Equation P := hP
    rw [WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero hPz]
    exact h _ _ ((WeierstrassCurve.Projective.equation_of_Z_ne_zero hPz).mp hE)

theorem nonsingular_of_equation_of_ne_zero_of_Δ_ne_zero {F : Type*} [Field F]
    {V : WeierstrassCurve.Projective F} (hΔ : V.Δ ≠ 0)
    {P : Fin 3 → F} (hP : V.Equation P) (hP0 : P ≠ 0) :
    V.Nonsingular P :=
  nonsingular_of_equation_of_forall_affine_nonsingular
    (fun _ _ hab => (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hab)
    hP hP0

theorem nonsingular_of_equation_of_ne_zero {F : Type*} [Field F]
    {V : WeierstrassCurve.Projective F} [V.IsElliptic]
    {P : Fin 3 → F} (hP : V.Equation P) (hP0 : P ≠ 0) :
    V.Nonsingular P :=
  nonsingular_of_equation_of_ne_zero_of_Δ_ne_zero (WeierstrassCurve.isUnit_Δ V).ne_zero hP hP0

end ProjWeierstrassDehomog

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime HomogeneousLocalization

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_pbac_mk_X_mem_one_CR kw_pbac_irrelevant_le_span_mk_X_CR kw_pbac_awayι_comp_projModelStrCR exists_zChartAway_equiv_coordinateRing exists_yChartAway_equiv_coordinateRing"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

def srd1_pmsCR_zCofactor (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
    - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2

theorem srd1_pmsCR_polynomial_add_X0_cube
    (V : WeierstrassCurve.Projective R) :
    V.polynomial + X 0 ^ 3 = X 2 * srd1_pmsCR_zCofactor V := by
  rw [WeierstrassCurve.Projective.polynomial, srd1_pmsCR_zCofactor]
  ring

theorem srd1_pmsCR_mk_X0_cube_mem_span_mk_X2
    (V : WeierstrassCurve.Projective R) :
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 0 : MvPolynomial (Fin 3) R)) ^ 3
      ∈ Ideal.span {Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X 2 : MvPolynomial (Fin 3) R)} := by
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal)
    (srd1_pmsCR_polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  rw [hid, Ideal.mem_span_singleton]
  exact ⟨_, rfl⟩

theorem srd1_pmsCR_not_both_in_ideal (V : WeierstrassCurve.Projective R)
    (x : Proj (projModelGradingCR V))
    (h1 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 1 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal)
    (h2 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 2 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal) :
    False := by
  have h0cube : (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 0 : MvPolynomial (Fin 3) R)) ^ 3 ∈ x.asHomogeneousIdeal.toIdeal :=
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h2))
      (srd1_pmsCR_mk_X0_cube_mem_span_mk_X2 V)
  have h0 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
      (X 0 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal :=
    x.isPrime.mem_of_pow_mem 3 h0cube
  have hspan : Ideal.span (Set.range fun i : Fin 3 =>
        Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X i : MvPolynomial (Fin 3) R)) ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz =>
    hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem srd1_pmsCR_awayι_jointly_surjective
    (V : WeierstrassCurve.Projective R) (x : Proj (projModelGradingCR V)) :
    ∃ (i : Fin 2)
      (u : Spec (CommRingCat.of (HomogeneousLocalization.Away (projModelGradingCR V)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (X (![1, 2] i) : MvPolynomial (Fin 3) R))))),
      (Proj.awayι (projModelGradingCR V) _
          (kw_pbac_mk_X_mem_one_CR R V (![1, 2] i)) Nat.one_pos) u = x := by
  by_cases hZ : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
      (X 2 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal
  · by_cases hY : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 1 : MvPolynomial (Fin 3) R) ∈ x.asHomogeneousIdeal.toIdeal
    · exact (srd1_pmsCR_not_both_in_ideal V x hY hZ).elim
    · have hrange : x ∈ (Proj.awayι (projModelGradingCR V) _
          (kw_pbac_mk_X_mem_one_CR R V 1) Nat.one_pos).opensRange := by
        rw [Proj.opensRange_awayι]
        exact hY
      obtain ⟨u, hu⟩ := Scheme.Hom.mem_opensRange.mp hrange
      exact ⟨0, u, hu⟩
  · have hrange : x ∈ (Proj.awayι (projModelGradingCR V) _
        (kw_pbac_mk_X_mem_one_CR R V 2) Nat.one_pos).opensRange := by
      rw [Proj.opensRange_awayι]
      exact hZ
    obtain ⟨u, hu⟩ := Scheme.Hom.mem_opensRange.mp hrange
    exact ⟨1, u, hu⟩

noncomputable def srd1_pmsCR_openCover (V : WeierstrassCurve.Projective R) :
    (Proj (projModelGradingCR V)).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2)
    (fun i => Spec (CommRingCat.of (HomogeneousLocalization.Away (projModelGradingCR V)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X (![1, 2] i) : MvPolynomial (Fin 3) R)))))
    (fun i => Proj.awayι (projModelGradingCR V) _
      (kw_pbac_mk_X_mem_one_CR R V (![1, 2] i)) Nat.one_pos)
    (srd1_pmsCR_awayι_jointly_surjective V)

end WeierstrassProjModel

end

noncomputable section

open AlgebraicGeometry CategoryTheory ProjWeierstrassCubicPrime
p2m_open "MvPolynomial Polynomial AlgebraicGeometry.Polynomial"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_pbac_mk_X_mem_one_CR kw_pbac_irrelevant_le_span_mk_X_CR kw_pbac_awayι_comp_projModelStrCR exists_zChartAway_equiv_coordinateRing exists_yChartAway_equiv_coordinateRing"
p2m_open "WeierstrassProjModel"

variable {R : Type u} [CommRing R]

def srd1_acsCR_mkPartial (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial} :=
  Ideal.Quotient.mk _ (![V.toAffine.polynomialX, V.toAffine.polynomialY] j)

noncomputable def srd1_spdCR_toIterated :
    MvPolynomial (Fin 2) R →ₐ[R] Polynomial (Polynomial R) :=
  MvPolynomial.aeval ![Polynomial.C Polynomial.X, Polynomial.X]

noncomputable def srd1_spdCR_fromIteratedRH :
    Polynomial (Polynomial R) →+* MvPolynomial (Fin 2) R :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
    (MvPolynomial.X 1)

theorem srd1_spdCR_fromIterated_toIterated :
    (srd1_spdCR_fromIteratedRH (R := R)).comp
        (srd1_spdCR_toIterated (R := R)).toRingHom
      = RingHom.id (MvPolynomial (Fin 2) R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [srd1_spdCR_fromIteratedRH, srd1_spdCR_toIterated]
  · intro i
    fin_cases i <;>
      simp [srd1_spdCR_fromIteratedRH, srd1_spdCR_toIterated]

theorem srd1_spdCR_toIterated_fromIterated :
    (srd1_spdCR_toIterated (R := R)).toRingHom.comp
        (srd1_spdCR_fromIteratedRH (R := R))
      = RingHom.id (Polynomial (Polynomial R)) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp [srd1_spdCR_fromIteratedRH, srd1_spdCR_toIterated]
    · simp [srd1_spdCR_fromIteratedRH, srd1_spdCR_toIterated]
  · simp [srd1_spdCR_fromIteratedRH, srd1_spdCR_toIterated]

theorem srd1_spdCR_toIterated_bijective :
    Function.Bijective (srd1_spdCR_toIterated (R := R)) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    have := DFunLike.congr_fun (srd1_spdCR_fromIterated_toIterated (R := R)) a
    have hb := DFunLike.congr_fun (srd1_spdCR_fromIterated_toIterated (R := R)) b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RingHom.id_apply] at this hb
    rw [← this, ← hb, hab]
  · intro y
    refine ⟨srd1_spdCR_fromIteratedRH y, ?_⟩
    have := DFunLike.congr_fun (srd1_spdCR_toIterated_fromIterated (R := R)) y
    simpa [RingHom.comp_apply] using this

noncomputable def srd1_spdCR_bivariateEquiv :
    MvPolynomial (Fin 2) R ≃ₐ[R] Polynomial (Polynomial R) :=
  AlgEquiv.ofBijective (srd1_spdCR_toIterated (R := R))
    (srd1_spdCR_toIterated_bijective (R := R))

noncomputable def srd1_spdCR_W_mv (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 2) R :=
  (MvPolynomial.X 1) ^ 2
    + MvPolynomial.C V.toAffine.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.C V.toAffine.a₃ * MvPolynomial.X 1
    - ((MvPolynomial.X 0) ^ 3
        + MvPolynomial.C V.toAffine.a₂ * (MvPolynomial.X 0) ^ 2
        + MvPolynomial.C V.toAffine.a₄ * MvPolynomial.X 0
        + MvPolynomial.C V.toAffine.a₆)

theorem srd1_spdCR_algebraMap_polyPoly (r : R) :
    algebraMap R (Polynomial (Polynomial R)) r = Polynomial.C (Polynomial.C r) := by
  rw [IsScalarTower.algebraMap_apply R (Polynomial R) (Polynomial (Polynomial R)),
    Polynomial.algebraMap_eq, Polynomial.algebraMap_eq]

theorem srd1_spdCR_bivariateEquiv_W_mv (V : WeierstrassCurve.Projective R) :
    srd1_spdCR_bivariateEquiv (R := R) (srd1_spdCR_W_mv V)
      = V.toAffine.polynomial := by
  simp only [srd1_spdCR_bivariateEquiv, AlgEquiv.ofBijective_apply,
    srd1_spdCR_toIterated, srd1_spdCR_W_mv,
    map_sub, map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    WeierstrassCurve.Affine.polynomial, Matrix.cons_val_zero, Matrix.cons_val_one,
    srd1_spdCR_algebraMap_polyPoly]
  ring

theorem srd1_spdCR_bivariateEquiv_pderiv0_W_mv
    (V : WeierstrassCurve.Projective R) :
    srd1_spdCR_bivariateEquiv (R := R)
        (MvPolynomial.pderiv 0 (srd1_spdCR_W_mv V))
      = V.toAffine.polynomialX := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [srd1_spdCR_W_mv, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne h10, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    srd1_spdCR_bivariateEquiv, AlgEquiv.ofBijective_apply,
    srd1_spdCR_toIterated, map_mul, map_pow, map_ofNat, map_natCast,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, WeierstrassCurve.Affine.polynomialX,
    Matrix.cons_val_zero, Matrix.cons_val_one, srd1_spdCR_algebraMap_polyPoly]
  push_cast
  ring

theorem srd1_spdCR_bivariateEquiv_pderiv1_W_mv
    (V : WeierstrassCurve.Projective R) :
    srd1_spdCR_bivariateEquiv (R := R)
        (MvPolynomial.pderiv 1 (srd1_spdCR_W_mv V))
      = V.toAffine.polynomialY := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp only [srd1_spdCR_W_mv, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne h01, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    srd1_spdCR_bivariateEquiv, AlgEquiv.ofBijective_apply,
    srd1_spdCR_toIterated, map_mul, map_pow, map_ofNat, map_natCast, sub_zero,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, WeierstrassCurve.Affine.polynomialY,
    Matrix.cons_val_zero, Matrix.cons_val_one, srd1_spdCR_algebraMap_polyPoly]
  push_cast
  ring

theorem srd1_spdCR_bivariateEquiv_pderiv_W_mv
    (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    srd1_spdCR_bivariateEquiv (R := R)
        (MvPolynomial.pderiv j (srd1_spdCR_W_mv V))
      = ![V.toAffine.polynomialX, V.toAffine.polynomialY] j := by
  fin_cases j
  · exact srd1_spdCR_bivariateEquiv_pderiv0_W_mv V
  · exact srd1_spdCR_bivariateEquiv_pderiv1_W_mv V

theorem srd1_spdCR_span_map (V : WeierstrassCurve.Projective R) :
    Ideal.span {V.toAffine.polynomial}
      = (Ideal.span (Set.range (fun _ : Fin 1 => srd1_spdCR_W_mv V))).map
          ((srd1_spdCR_bivariateEquiv (R := R) :
            MvPolynomial (Fin 2) R →+* Polynomial (Polynomial R))) := by
  rw [Set.range_const, Ideal.map_span, Set.image_singleton]
  exact congrArg (fun z => Ideal.span {z})
    (srd1_spdCR_bivariateEquiv_W_mv V).symm

noncomputable def srd1_spdCR_quotEquiv (V : WeierstrassCurve.Projective R) :
    (MvPolynomial (Fin 2) R
        ⧸ Ideal.span (Set.range (fun _ : Fin 1 => srd1_spdCR_W_mv V)))
      ≃ₐ[R] (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) :=
  Ideal.quotientEquivAlg
    (Ideal.span (Set.range (fun _ : Fin 1 => srd1_spdCR_W_mv V)))
    (Ideal.span {V.toAffine.polynomial})
    (srd1_spdCR_bivariateEquiv (R := R))
    (srd1_spdCR_span_map V)

theorem srd1_spdCR_quotEquiv_mk (V : WeierstrassCurve.Projective R)
    (p : MvPolynomial (Fin 2) R) :
    srd1_spdCR_quotEquiv V (Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk _ (srd1_spdCR_bivariateEquiv (R := R) p) :=
  rfl

noncomputable def srd1_spdCR_P₀ (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    Algebra.PreSubmersivePresentation R
      (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) (Fin 2) (Fin 1) :=
  (Algebra.PreSubmersivePresentation.naive
    (v := fun _ : Fin 1 => srd1_spdCR_W_mv V)
    (fun _ : Fin 1 => j) (Function.injective_of_subsingleton _)).ofAlgEquiv
    (srd1_spdCR_quotEquiv V)

theorem srd1_spdCR_P₀_jacobian (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    (srd1_spdCR_P₀ V j).jacobian = srd1_acsCR_mkPartial V j := by
  classical
  rw [srd1_spdCR_P₀, Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, Fin.default_eq_zero]
  show srd1_spdCR_quotEquiv V
      (Ideal.Quotient.mk _ (MvPolynomial.pderiv j (srd1_spdCR_W_mv V)))
    = srd1_acsCR_mkPartial V j
  rw [srd1_spdCR_quotEquiv_mk,
    srd1_spdCR_bivariateEquiv_pderiv_W_mv, srd1_acsCR_mkPartial]

noncomputable def srd1_spdCR_compPres (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    Algebra.PreSubmersivePresentation R
      (Localization.Away (srd1_acsCR_mkPartial V j))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) :=
  (Algebra.PreSubmersivePresentation.localizationAway
    (Localization.Away (srd1_acsCR_mkPartial V j))
    (srd1_acsCR_mkPartial V j)).comp (srd1_spdCR_P₀ V j)

theorem srd1_spdCR_compPres_jacobian_isUnit (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    IsUnit (srd1_spdCR_compPres V j).jacobian := by
  rw [srd1_spdCR_compPres,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,
    srd1_spdCR_P₀_jacobian, Algebra.smul_def]
  exact (IsLocalization.Away.algebraMap_isUnit (srd1_acsCR_mkPartial V j)).mul
    (IsLocalization.Away.algebraMap_isUnit (srd1_acsCR_mkPartial V j))

noncomputable def srd1_spdCR_submersive (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    Algebra.SubmersivePresentation R
      (Localization.Away (srd1_acsCR_mkPartial V j))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) where
  __ := srd1_spdCR_compPres V j
  jacobian_isUnit := srd1_spdCR_compPres_jacobian_isUnit V j

end WeierstrassProjModel

end

noncomputable section

open AlgebraicGeometry CategoryTheory ProjWeierstrassCubicPrime
p2m_open "Polynomial AlgebraicGeometry.Polynomial WeierstrassCurve"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_pbac_mk_X_mem_one_CR kw_pbac_irrelevant_le_span_mk_X_CR kw_pbac_awayι_comp_projModelStrCR exists_zChartAway_equiv_coordinateRing exists_yChartAway_equiv_coordinateRing"
p2m_open "WeierstrassProjModel"

variable {R : Type u} [CommRing R]

theorem srd1_pstCR_algHom_eq_evalEval_map {L : Type*} [CommRing L] [Algebra R L]
    (π : Polynomial (Polynomial R) →ₐ[R] L) (p : Polynomial (Polynomial R)) :
    π p = (p.map (Polynomial.mapRingHom (algebraMap R L))).evalEval
      (π (Polynomial.C Polynomial.X)) (π Polynomial.X) := by
  have hrh :
      (π : Polynomial (Polynomial R) →+* L)
        = (Polynomial.evalEvalRingHom (π (Polynomial.C Polynomial.X)) (π Polynomial.X)).comp
            (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap R L))) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r
        have hπr : π (Polynomial.C (Polynomial.C r)) = algebraMap R L r := by
          rw [← srd1_spdCR_algebraMap_polyPoly r]; exact π.commutes r
        simp [hπr]
      · simp
    · simp
  exact DFunLike.congr_fun hrh p

theorem srd1_pstCR_algHom_polynomial {L : Type*} [CommRing L] [Algebra R L]
    (π : Polynomial (Polynomial R) →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π V.toAffine.polynomial
      = (V.toAffine.map (algebraMap R L)).polynomial.evalEval
          (π (Polynomial.C Polynomial.X)) (π Polynomial.X) := by
  rw [srd1_pstCR_algHom_eq_evalEval_map π,
    ← WeierstrassCurve.Affine.map_polynomial]

theorem srd1_pstCR_algHom_polynomialX {L : Type*} [CommRing L] [Algebra R L]
    (π : Polynomial (Polynomial R) →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π V.toAffine.polynomialX
      = (V.toAffine.map (algebraMap R L)).polynomialX.evalEval
          (π (Polynomial.C Polynomial.X)) (π Polynomial.X) := by
  rw [srd1_pstCR_algHom_eq_evalEval_map π,
    ← WeierstrassCurve.Affine.map_polynomialX]

theorem srd1_pstCR_algHom_polynomialY {L : Type*} [CommRing L] [Algebra R L]
    (π : Polynomial (Polynomial R) →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π V.toAffine.polynomialY
      = (V.toAffine.map (algebraMap R L)).polynomialY.evalEval
          (π (Polynomial.C Polynomial.X)) (π Polynomial.X) := by
  rw [srd1_pstCR_algHom_eq_evalEval_map π,
    ← WeierstrassCurve.Affine.map_polynomialY]

theorem srd1_pstCR_no_maximal_over_triple
    (V : WeierstrassCurve.Projective R) [V.IsElliptic]
    (M : Ideal (Polynomial (Polynomial R))) (hmax : M.IsMaximal)
    (hW : V.toAffine.polynomial ∈ M) (hX : V.toAffine.polynomialX ∈ M)
    (hY : V.toAffine.polynomialY ∈ M) :
    False := by
  classical
  haveI : Nontrivial (Polynomial (Polynomial R) ⧸ M) :=
    Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top

  have hπW : (Ideal.Quotient.mkₐ R M) V.toAffine.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hW
  have hπX : (Ideal.Quotient.mkₐ R M) V.toAffine.polynomialX = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hX
  have hπY : (Ideal.Quotient.mkₐ R M) V.toAffine.polynomialY = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hY

  have hEq : (V.toAffine.map (algebraMap R (Polynomial (Polynomial R) ⧸ M))).Equation
      ((Ideal.Quotient.mkₐ R M) (Polynomial.C Polynomial.X))
      ((Ideal.Quotient.mkₐ R M) Polynomial.X) := by
    have h := @srd1_pstCR_algHom_polynomial R _ (Polynomial (Polynomial R) ⧸ M)
      inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
    rw [hπW] at h
    exact h.symm
  have hX0 : (V.toAffine.map (algebraMap R
      (Polynomial (Polynomial R) ⧸ M))).polynomialX.evalEval
      ((Ideal.Quotient.mkₐ R M) (Polynomial.C Polynomial.X))
      ((Ideal.Quotient.mkₐ R M) Polynomial.X) = 0 := by
    have h := @srd1_pstCR_algHom_polynomialX R _ (Polynomial (Polynomial R) ⧸ M)
      inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
    rw [hπX] at h
    exact h.symm
  have hY0 : (V.toAffine.map (algebraMap R
      (Polynomial (Polynomial R) ⧸ M))).polynomialY.evalEval
      ((Ideal.Quotient.mkₐ R M) (Polynomial.C Polynomial.X))
      ((Ideal.Quotient.mkₐ R M) Polynomial.X) = 0 := by
    have h := @srd1_pstCR_algHom_polynomialY R _ (Polynomial (Polynomial R) ⧸ M)
      inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
    rw [hπY] at h
    exact h.symm

  rcases ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp hEq).2 with h | h
  · exact h hX0
  · exact h hY0

theorem srd1_pstCR_affinePartialsSpanTopCR
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    Ideal.span (Set.range (srd1_acsCR_mkPartial V)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨m, hmax, hle⟩ :=
    Ideal.exists_le_maximal (Ideal.span (Set.range (srd1_acsCR_mkPartial V))) hne

  let M : Ideal (Polynomial (Polynomial R)) :=
    Ideal.comap (Ideal.Quotient.mk (Ideal.span {V.toAffine.polynomial})) m
  have hMmax : M.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hWM : V.toAffine.polynomial ∈ M := by
    simp only [M, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
    exact Submodule.zero_mem m
  have hXM : V.toAffine.polynomialX ∈ M := by
    have h0 : srd1_acsCR_mkPartial V 0 ∈ m := hle (Ideal.subset_span ⟨0, rfl⟩)
    simpa only [srd1_acsCR_mkPartial, Matrix.cons_val_zero, M,
      Ideal.mem_comap] using h0
  have hYM : V.toAffine.polynomialY ∈ M := by
    have h1 : srd1_acsCR_mkPartial V 1 ∈ m := hle (Ideal.subset_span ⟨1, rfl⟩)
    simpa only [srd1_acsCR_mkPartial, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
      M, Ideal.mem_comap] using h1
  exact srd1_pstCR_no_maximal_over_triple V M hMmax hWM hXM hYM

end WeierstrassProjModel

end

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ProjWeierstrassCubicPrime ProjWeierstrassDehomog

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_pbac_mk_X_mem_one_CR kw_pbac_irrelevant_le_span_mk_X_CR kw_pbac_awayι_comp_projModelStrCR exists_zChartAway_equiv_coordinateRing exists_yChartAway_equiv_coordinateRing"
p2m_open "WeierstrassProjModel"

variable {R : Type u} [CommRing R]

theorem srd1_ydeCR_algHom_C {L : Type*} [CommRing L] [Algebra R L]
    (π : MvPolynomial (Fin 2) R →ₐ[R] L) (r : R) :
    π (MvPolynomial.C r) = algebraMap R L r := by
  rw [← MvPolynomial.algebraMap_eq]; exact π.commutes r

noncomputable def srd1_ydeCR_W_Y (V : WeierstrassCurve.Projective R) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval
    (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) R) V.polynomial

theorem srd1_ydeCR_W_Y_eq (V : WeierstrassCurve.Projective R) :
    srd1_ydeCR_W_Y V
      = MvPolynomial.X 1
        + MvPolynomial.C V.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
        + MvPolynomial.C V.a₃ * (MvPolynomial.X 1) ^ 2
        - ((MvPolynomial.X 0) ^ 3
            + MvPolynomial.C V.a₂ * (MvPolynomial.X 0) ^ 2 * MvPolynomial.X 1
            + MvPolynomial.C V.a₄ * MvPolynomial.X 0 * (MvPolynomial.X 1) ^ 2
            + MvPolynomial.C V.a₆ * (MvPolynomial.X 1) ^ 3) := by
  rw [srd1_ydeCR_W_Y, WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

abbrev srd1_ydeCR_coordRing (V : WeierstrassCurve.Projective R) : Type u :=
  MvPolynomial (Fin 2) R
    ⧸ Ideal.span (Set.range (fun _ : Fin 1 => srd1_ydeCR_W_Y V))

def srd1_ydeCR_mkYPartial (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    srd1_ydeCR_coordRing V :=
  Ideal.Quotient.mk _ (MvPolynomial.pderiv j (srd1_ydeCR_W_Y V))

theorem srd1_ydeCR_algHom_W_Y {L : Type*} [CommRing L] [Algebra R L]
    (π : MvPolynomial (Fin 2) R →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π (srd1_ydeCR_W_Y V)
      = MvPolynomial.eval
          ![π (MvPolynomial.X 0), 1, π (MvPolynomial.X 1)]
          (V.map (algebraMap R L)).polynomial := by
  rw [WeierstrassCurve.Projective.eval_polynomial]
  simp only [srd1_ydeCR_W_Y_eq, map_sub, map_add, map_mul, map_pow,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons,
    WeierstrassCurve.map, srd1_ydeCR_algHom_C]
  ring

theorem srd1_ycdCR_algHom_pderiv0 {L : Type*} [CommRing L] [Algebra R L]
    (π : MvPolynomial (Fin 2) R →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π (MvPolynomial.pderiv 0 (srd1_ydeCR_W_Y V))
      = MvPolynomial.eval
          ![π (MvPolynomial.X 0), 1, π (MvPolynomial.X 1)]
          (V.map (algebraMap R L)).polynomialX := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [WeierstrassCurve.Projective.eval_polynomialX]
  simp only [srd1_ydeCR_W_Y_eq, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne h10, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    map_mul, map_pow, map_natCast,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons,
    WeierstrassCurve.map, srd1_ydeCR_algHom_C]
  push_cast
  ring

theorem srd1_ycdCR_algHom_pderiv1 {L : Type*} [CommRing L] [Algebra R L]
    (π : MvPolynomial (Fin 2) R →ₐ[R] L) (V : WeierstrassCurve.Projective R) :
    π (MvPolynomial.pderiv 1 (srd1_ydeCR_W_Y V))
      = MvPolynomial.eval
          ![π (MvPolynomial.X 0), 1, π (MvPolynomial.X 1)]
          (V.map (algebraMap R L)).polynomialZ := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [WeierstrassCurve.Projective.eval_polynomialZ]
  simp only [srd1_ydeCR_W_Y_eq, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne h01, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    map_mul, map_pow, map_natCast, map_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons,
    WeierstrassCurve.map, srd1_ydeCR_algHom_C]
  push_cast
  ring

noncomputable def srd1_ycdCR_P₀ (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    Algebra.PreSubmersivePresentation R (srd1_ydeCR_coordRing V) (Fin 2) (Fin 1) :=
  Algebra.PreSubmersivePresentation.naive (v := fun _ : Fin 1 => srd1_ydeCR_W_Y V)
    (fun _ : Fin 1 => j) (Function.injective_of_subsingleton _)

theorem srd1_ycdCR_P₀_jacobian (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    (srd1_ycdCR_P₀ V j).jacobian = srd1_ydeCR_mkYPartial V j := by
  classical
  rw [srd1_ycdCR_P₀, Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, Fin.default_eq_zero]
  rfl

noncomputable def srd1_ycdCR_compPres (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    Algebra.PreSubmersivePresentation R
      (Localization.Away (srd1_ydeCR_mkYPartial V j))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) :=
  (Algebra.PreSubmersivePresentation.localizationAway
    (Localization.Away (srd1_ydeCR_mkYPartial V j))
    (srd1_ydeCR_mkYPartial V j)).comp (srd1_ycdCR_P₀ V j)

theorem srd1_ycdCR_compPres_jacobian_isUnit (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    IsUnit (srd1_ycdCR_compPres V j).jacobian := by
  rw [srd1_ycdCR_compPres,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,
    srd1_ycdCR_P₀_jacobian, Algebra.smul_def]
  exact (IsLocalization.Away.algebraMap_isUnit (srd1_ydeCR_mkYPartial V j)).mul
    (IsLocalization.Away.algebraMap_isUnit (srd1_ydeCR_mkYPartial V j))

noncomputable def srd1_ycdCR_submersive (V : WeierstrassCurve.Projective R)
    (j : Fin 2) :
    Algebra.SubmersivePresentation R
      (Localization.Away (srd1_ydeCR_mkYPartial V j))
      (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) where
  __ := srd1_ycdCR_compPres V j
  jacobian_isUnit := srd1_ycdCR_compPres_jacobian_isUnit V j

theorem srd1_ycdCR_rep_YOne_ne_zero {L : Type*} [CommRing L] [Nontrivial L]
    (a b : L) :
    (![a, 1, b] : Fin 3 → L) ≠ 0 := by
  intro h
  have h1 : (![a, 1, b] : Fin 3 → L) 1 = 0 := by rw [h]; rfl
  simp only [Matrix.cons_val_one] at h1
  exact one_ne_zero h1

theorem srd1_ycdCR_not_singular_at_YOne {L : Type*} [Field L]
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] (φ : R →+* L) (x₀ z₀ : L)
    (hW : MvPolynomial.eval ![x₀, 1, z₀] (V.map φ).polynomial = 0)
    (hX : MvPolynomial.eval ![x₀, 1, z₀] (V.map φ).polynomialX = 0)
    (hZ : MvPolynomial.eval ![x₀, 1, z₀] (V.map φ).polynomialZ = 0) :
    False := by
  have hns := ProjWeierstrassDehomog.nonsingular_of_equation_of_ne_zero
    (V := V.map φ) hW (srd1_ycdCR_rep_YOne_ne_zero x₀ z₀)
  have hY : MvPolynomial.eval ![x₀, 1, z₀] (V.map φ).polynomialY = 0 := by
    have hEul := WeierstrassCurve.Projective.polynomial_relation (W' := V.map φ) ![x₀, 1, z₀]
    simp only [hW, hX, hZ, mul_zero, zero_add, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_mul] at hEul
    exact hEul.symm
  rcases hns.2 with h | h | h
  · exact h hX
  · exact h hY
  · exact h hZ

theorem srd1_ycdCR_no_maximal_over_triple
    (V : WeierstrassCurve.Projective R) [V.IsElliptic]
    (M : Ideal (MvPolynomial (Fin 2) R)) (hmax : M.IsMaximal)
    (hW : srd1_ydeCR_W_Y V ∈ M)
    (hX : MvPolynomial.pderiv 0 (srd1_ydeCR_W_Y V) ∈ M)
    (hZ : MvPolynomial.pderiv 1 (srd1_ydeCR_W_Y V) ∈ M) :
    False := by
  classical
  haveI := hmax
  letI : Field (MvPolynomial (Fin 2) R ⧸ M) := Ideal.Quotient.field M

  have hbrW := @srd1_ydeCR_algHom_W_Y R _ (MvPolynomial (Fin 2) R ⧸ M)
    inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
  have hbrX := @srd1_ycdCR_algHom_pderiv0 R _ (MvPolynomial (Fin 2) R ⧸ M)
    inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
  have hbrZ := @srd1_ycdCR_algHom_pderiv1 R _ (MvPolynomial (Fin 2) R ⧸ M)
    inferInstance inferInstance (Ideal.Quotient.mkₐ R M) V
  simp only [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hW,
    Ideal.Quotient.eq_zero_iff_mem.mpr hX, Ideal.Quotient.eq_zero_iff_mem.mpr hZ]
    at hbrW hbrX hbrZ
  exact srd1_ycdCR_not_singular_at_YOne V
    (algebraMap R (MvPolynomial (Fin 2) R ⧸ M)) _ _ hbrW.symm hbrX.symm hbrZ.symm

theorem srd1_ycdCR_partialsSpanTop
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    Ideal.span (Set.range (srd1_ydeCR_mkYPartial V)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨m, hmax, hle⟩ :=
    Ideal.exists_le_maximal (Ideal.span (Set.range (srd1_ydeCR_mkYPartial V))) hne
  let M : Ideal (MvPolynomial (Fin 2) R) :=
    Ideal.comap (Ideal.Quotient.mk
      (Ideal.span (Set.range (fun _ : Fin 1 => srd1_ydeCR_W_Y V)))) m
  have hMmax : M.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hWM : srd1_ydeCR_W_Y V ∈ M := by
    have hspan : srd1_ydeCR_W_Y V
        ∈ Ideal.span (Set.range (fun _ : Fin 1 => srd1_ydeCR_W_Y V)) :=
      Ideal.subset_span (Set.mem_range_self (0 : Fin 1))
    simp only [M, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hspan]
    exact Submodule.zero_mem m
  have hXM : MvPolynomial.pderiv 0 (srd1_ydeCR_W_Y V) ∈ M := by
    have h0 : srd1_ydeCR_mkYPartial V 0 ∈ m := hle (Ideal.subset_span ⟨0, rfl⟩)
    simpa only [srd1_ydeCR_mkYPartial, M, Ideal.mem_comap] using h0
  have hZM : MvPolynomial.pderiv 1 (srd1_ydeCR_W_Y V) ∈ M := by
    have h1 : srd1_ydeCR_mkYPartial V 1 ∈ m := hle (Ideal.subset_span ⟨1, rfl⟩)
    simpa only [srd1_ydeCR_mkYPartial, M, Ideal.mem_comap] using h1
  exact srd1_ycdCR_no_maximal_over_triple V M hMmax hWM hXM hZM

end WeierstrassProjModel

end

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR kw_pbac_awayAlgebra kw_pbac_mk_X_mem_one_CR kw_pbac_irrelevant_le_span_mk_X_CR kw_pbac_awayι_comp_projModelStrCR exists_zChartAway_equiv_coordinateRing exists_yChartAway_equiv_coordinateRing"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

theorem srd1_spdCR_leg_isStandardSmoothOfRelativeDimension_one
    (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R
      (Localization.Away (srd1_acsCR_mkPartial V j)) :=
  (srd1_spdCR_submersive V j).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

theorem srd1_ycdCR_leg_isStandardSmoothOfRelativeDimension_one
    (V : WeierstrassCurve.Projective R) (j : Fin 2) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R
      (Localization.Away (srd1_ydeCR_mkYPartial V j)) :=
  (srd1_ycdCR_submersive V j).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

theorem srd1_locally_affineZ (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial})) := by
  refine RingHom.locally_of_exists RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    _ (srd1_acsCR_mkPartial V) (srd1_pstCR_affinePartialsSpanTopCR V)
    (fun j => Localization.Away (srd1_acsCR_mkPartial V j)) fun j => ?_
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact srd1_spdCR_leg_isStandardSmoothOfRelativeDimension_one V j

theorem srd1_locally_affineY (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (srd1_ydeCR_coordRing V)) := by
  refine RingHom.locally_of_exists RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    _ (srd1_ydeCR_mkYPartial V) (srd1_ycdCR_partialsSpanTop V)
    (fun j => Localization.Away (srd1_ydeCR_mkYPartial V j)) fun j => ?_
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact srd1_ycdCR_leg_isStandardSmoothOfRelativeDimension_one V j

attribute [local instance] kw_pbac_awayAlgebra

theorem srd1_chartZ_smoothOfRelativeDimension_one
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    SmoothOfRelativeDimension 1
      (Proj.awayι (projModelGradingCR V)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X 2 : MvPolynomial (Fin 3) R))
          (kw_pbac_mk_X_mem_one_CR R V 2) one_pos
        ≫ projModelStrCR V) := by
  rw [kw_pbac_awayι_comp_projModelStrCR R V 2,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1), CommRingCat.hom_ofHom]
  obtain ⟨f, hbij, hcomp, -⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have h' := (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).1 _ e.symm (srd1_locally_affineZ V)
  have key : e.symm.toRingHom.comp
        (algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}))
      = algebraMap R _ := by
    rw [← hcomp]
    exact RingHom.ext fun x => e.symm_apply_apply _
  rw [key] at h'
  exact h'

theorem srd1_chartY_smoothOfRelativeDimension_one
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    SmoothOfRelativeDimension 1
      (Proj.awayι (projModelGradingCR V)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X 1 : MvPolynomial (Fin 3) R))
          (kw_pbac_mk_X_mem_one_CR R V 1) one_pos
        ≫ projModelStrCR V) := by
  rw [kw_pbac_awayι_comp_projModelStrCR R V 1,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1), CommRingCat.hom_ofHom]
  obtain ⟨f, hbij, hcomp, -⟩ := WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have h' := (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).1 _ e.symm (srd1_locally_affineY V)

  have key : e.symm.toRingHom.comp (algebraMap R (srd1_ydeCR_coordRing V))
      = algebraMap R _ := by
    change e.symm.toRingHom.comp (algebraMap R (MvPolynomial (Fin 2) R ⧸ Ideal.span
        (Set.range fun _ : Fin 1 => MvPolynomial.aeval
          (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) R)
          V.polynomial))) = _
    rw [← hcomp]
    exact RingHom.ext fun x => e.symm_apply_apply _
  rw [key] at h'
  exact h'

theorem srd1_projModelStrCR_smoothOfRelativeDimension_one
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    SmoothOfRelativeDimension 1 (projModelStrCR V) := by
  have hleg : ∀ i : Fin 2, SmoothOfRelativeDimension 1
      (Proj.awayι (projModelGradingCR V)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X (![1, 2] i) : MvPolynomial (Fin 3) R))
          (kw_pbac_mk_X_mem_one_CR R V (![1, 2] i)) Nat.one_pos
        ≫ projModelStrCR V) := by
    intro i
    fin_cases i
    · exact srd1_chartY_smoothOfRelativeDimension_one V
    · exact srd1_chartZ_smoothOfRelativeDimension_one V
  exact IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (srd1_pmsCR_openCover V) hleg

end WeierstrassProjModel

end

open AlgebraicGeometry _root_.WeierstrassProjModel _root_.P2MW.S_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one.WeierstrassProjModel in
theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    SmoothOfRelativeDimension 1 (projModelStrCR V) :=
  srd1_projModelStrCR_smoothOfRelativeDimension_one V

end S_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one (solution)

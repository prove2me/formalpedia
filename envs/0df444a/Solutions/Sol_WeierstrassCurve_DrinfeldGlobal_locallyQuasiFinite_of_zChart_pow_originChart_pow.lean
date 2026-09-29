-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.locallyQuasiFinite_of_zChart_pow_originChart_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d9823ffd-7358-5f6d-9d64-aca8731b6099

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Theorems.Thm_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_projMap_comp_projModelStrCR_of_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_locallyQuasiFinite_of_zChart_pow_originChart_pow

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

namespace RelFrob

noncomputable def zStr {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T) : T →+* ZChartRing V :=
  (fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))

theorem zChartι_comp_projModelStrCR {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T) :
    zChartι V ≫ projModelStrCR V = Spec.map (CommRingCat.ofHom (zStr V)) := by
  rw [projModelStrCR, ← Category.assoc]
  erw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  rfl

theorem zChart_ringHom_ext {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T) {B : Type} [CommRing B]
    (g₁ g₂ : ZChartRing V →+* B) (h0 : g₁.comp (zStr V) = g₂.comp (zStr V))
    (hx : g₁ (xOverZ V) = g₂ (xOverZ V)) (hy : g₁ (yOverZ V) = g₂ (yOverZ V)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.head_cons] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = zStr V r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext x
    have := RingHom.congr_fun h' (e x)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
      exact RingHom.congr_fun h0 r
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hx']
      exact hx
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hy']
    exact hy

section zalg

theorem zStr_finitePresentation {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T) :
    (zStr V).FinitePresentation := by
  classical
  obtain ⟨f, hbij, hcomp, -⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  let e0 := RingEquiv.ofBijective f hbij
  have hFP : (algebraMap T (Polynomial (Polynomial T) ⧸ Ideal.span {WeierstrassCurve.Affine.polynomial V.toAffine})).FinitePresentation := by
    rw [RingHom.finitePresentation_algebraMap]
    exact Algebra.FinitePresentation.quotient
      ⟨{WeierstrassCurve.Affine.polynomial V.toAffine}, by rw [Finset.coe_singleton]⟩
  have hcomp' : zStr V = e0.symm.toRingHom.comp
      (algebraMap T (Polynomial (Polynomial T) ⧸ Ideal.span {WeierstrassCurve.Affine.polynomial V.toAffine})) := by
    refine RingHom.ext fun t => ?_
    rw [RingHom.comp_apply]
    apply e0.injective
    change _ = e0 (e0.symm _)
    rw [RingEquiv.apply_symm_apply]
    exact RingHom.congr_fun hcomp t
  rw [hcomp']
  refine RingHom.FinitePresentation.comp_surjective hFP e0.symm.surjective ?_
  rw [show RingHom.ker e0.symm.toRingHom = ⊥ from (RingHom.injective_iff_ker_eq_bot _).mp e0.symm.injective]
  exact Submodule.fg_bot

theorem zStr_finiteType {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T) : (zStr V).FiniteType :=
  RingHom.FiniteType.of_finitePresentation (zStr_finitePresentation V)

variable (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [CharP T q]

theorem exists_frobTwist_zChart (V : WeierstrassCurve.Projective T) :
    ∃ a : ZChartRing V →+* ZChartRing (V.map (frobenius T q)),
      a (xOverZ V) = xOverZ (V.map (frobenius T q)) ∧ a (yOverZ V) = yOverZ (V.map (frobenius T q)) ∧
      a.comp (zStr V) = (zStr (V.map (frobenius T q))).comp (frobenius T q) := by
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom V (frobenius T q)
  obtain ⟨a, ha, hax, hay⟩ :=
    exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota V (frobenius T q) φ hφ hcoef
  refine ⟨a, hax, hay, ?_⟩
  have h1 := congrArg (· ≫ projModelStrCR V) ha
  simp only [Category.assoc] at h1
  rw [projMap_comp_projModelStrCR_of_isCoefficientHom V (frobenius T q) φ hφ hcoef, ← Category.assoc,
    zChartι_comp_projModelStrCR, zChartι_comp_projModelStrCR, ← Spec.map_comp, ← Spec.map_comp] at h1
  exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h1)).symm

theorem charP_of_zStr {T : Type} [CommRing T] (q : ℕ) [Fact q.Prime] [CharP T q]
    (V : WeierstrassCurve.Projective T) [Nontrivial (ZChartRing V)] : CharP (ZChartRing V) q := by
  refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
  have h := map_natCast (zStr V) q
  rw [CharP.cast_eq_zero, map_zero] at h
  exact h.symm

variable (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective)
    (hx : ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q)
    (hy : ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q)
    (hcomp : zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)

include hΦ hcomp in

theorem psiZ_comp_zStr : ψ.comp (zStr (W.map (frobenius T q)).toProjective) = zStr W.toProjective := by
  have h1 : zChartι W.toProjective ≫ Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective
      = zChartι W.toProjective ≫ projModelStrCR W.toProjective := by rw [hΦ]
  rw [← Category.assoc, hcomp, Category.assoc, zChartι_comp_projModelStrCR, zChartι_comp_projModelStrCR,
    ← Spec.map_comp] at h1
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

include hΦ hx hy hcomp in

theorem psiZ_frobenius :
    ∃ a : ZChartRing W.toProjective →+* ZChartRing (W.map (frobenius T q)).toProjective,
      (∀ b, ψ (a b) = b ^ q) ∧ (∀ b', a (ψ b') = b' ^ q) := by
  obtain ⟨a, hax, hay, hasl⟩ := exists_frobTwist_zChart q T W.toProjective
  have hlin := psiZ_comp_zStr q T W Φ hΦ ψ hcomp
  refine ⟨a, ?_, ?_⟩
  · rcases subsingleton_or_nontrivial (ZChartRing W.toProjective) with hB | hB
    · intro b; exact Subsingleton.elim _ _
    · haveI := charP_of_zStr q W.toProjective
      have key : ψ.comp a = frobenius (ZChartRing W.toProjective) q := by
        apply zChart_ringHom_ext W.toProjective
        · rw [RingHom.comp_assoc, hasl, ← RingHom.comp_assoc, hlin]
          ext t
          simp only [RingHom.comp_apply, frobenius_def, map_pow]
        · rw [RingHom.comp_apply, hax, hx]; rfl
        · rw [RingHom.comp_apply, hay, hy]; rfl
      intro b
      exact RingHom.congr_fun key b
  · rcases subsingleton_or_nontrivial (ZChartRing (W.map (frobenius T q)).toProjective) with hB | hB
    · intro b; exact Subsingleton.elim _ _
    · haveI := charP_of_zStr q (W.map (frobenius T q)).toProjective
      have key : a.comp ψ = frobenius (ZChartRing (W.map (frobenius T q)).toProjective) q := by
        apply zChart_ringHom_ext (W.map (frobenius T q)).toProjective
        · rw [RingHom.comp_assoc, hlin, hasl]
          ext t
          simp only [RingHom.comp_apply, frobenius_def, map_pow]
        · rw [RingHom.comp_apply, hx, map_pow, hax]; rfl
        · rw [RingHom.comp_apply, hy, map_pow, hay]; rfl
      intro b
      exact RingHom.congr_fun key b

include hΦ hx hy hcomp in
theorem isIntegral_psiZ : ψ.IsIntegral := by
  obtain ⟨a, h1, -⟩ := psiZ_frobenius q T W Φ hΦ ψ hx hy hcomp
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  intro b
  refine ⟨Polynomial.X ^ q - Polynomial.C (a b), Polynomial.monic_X_pow_sub_C _ hq0, ?_⟩
  simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h1 b]

include hΦ hx hy hcomp in

theorem finite_psiZ : ψ.Finite :=
  RingHom.IsIntegral.to_finite (isIntegral_psiZ q T W Φ hΦ ψ hx hy hcomp)
    (RingHom.FiniteType.of_comp_finiteType (f := zStr (W.map (frobenius T q)).toProjective)
      (by rw [psiZ_comp_zStr q T W Φ hΦ ψ hcomp]; exact zStr_finiteType W.toProjective))

include hΦ hcomp in

theorem finitePresentation_psiZ : ψ.FinitePresentation :=
  RingHom.FinitePresentation.of_comp_finiteType (zStr (W.map (frobenius T q)).toProjective)
    (by rw [psiZ_comp_zStr q T W Φ hΦ ψ hcomp]; exact zStr_finitePresentation W.toProjective)
    (zStr_finiteType (W.map (frobenius T q)).toProjective)

include hΦ hx hy hcomp in

theorem isNilpotent_of_psiZ_eq_zero (b' : ZChartRing (W.map (frobenius T q)).toProjective) (h : ψ b' = 0) :
    IsNilpotent b' := by
  obtain ⟨a, -, h2⟩ := psiZ_frobenius q T W Φ hΦ ψ hx hy hcomp
  exact ⟨q, by rw [← h2 b', h, map_zero]⟩

end zalg

end RelFrob

noncomputable section

namespace RelFrobAlg

theorem surjective_comap_of_isIntegral_of_ker_le_nilradical {A B : Type u} [CommRing A] [CommRing B]
    (ψ : A →+* B) (hint : ψ.IsIntegral) (hker : ∀ a, ψ a = 0 → IsNilpotent a) :
    Function.Surjective (PrimeSpectrum.comap ψ) := by
  intro p
  letI : Algebra A B := ψ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hint⟩
  have hle : RingHom.ker (algebraMap A B) ≤ p.asIdeal := by
    intro a ha
    obtain ⟨n, hn⟩ := hker a ha
    exact p.isPrime.mem_of_pow_mem n (by rw [hn]; exact p.asIdeal.zero_mem)
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal B)
    (by intro a ha; exact hle (by simpa [RingHom.mem_ker, Ideal.mem_comap] using ha))
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

theorem surjective_specMap_base_of_isIntegral_of_ker_le_nilradical {A B : Type u} [CommRing A] [CommRing B]
    (ψ : A →+* B) (hint : ψ.IsIntegral) (hker : ∀ a, ψ a = 0 → IsNilpotent a) :
    Function.Surjective (Spec.map (CommRingCat.ofHom ψ)).base :=
  surjective_comap_of_isIntegral_of_ker_le_nilradical ψ hint hker

theorem isIntegral_of_pow_mem_range {A B : Type u} [CommRing A] [CommRing B] (ψ : A →+* B) (q : ℕ) (hq : 0 < q)
    (hpow : ∀ b : B, ∃ a, ψ a = b ^ q) : ψ.IsIntegral := by
  intro b
  obtain ⟨a, ha⟩ := hpow b
  refine ⟨Polynomial.X ^ q - Polynomial.C a, Polynomial.monic_X_pow_sub_C a hq.ne', ?_⟩
  simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, ha]

section originext

noncomputable def originStr {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T) : T →+* OriginChartRing V :=
  (fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))

theorem originChart_ringHom_ext {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T) {B : Type} [CommRing B]
    (g₁ g₂ : OriginChartRing V →+* B) (h0 : g₁.comp (originStr V) = g₂.comp (originStr V))
    (hx : g₁ (xOverY V) = g₂ (xOverY V)) (hz : g₁ (zOverY V) = g₂ (zOverY V)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have h0' : e.symm (Ideal.Quotient.mk _ (MvPolynomial.X 0)) = xOverY V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have h1' : e.symm (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = zOverY V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 2)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 2))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (MvPolynomial.C r)) = originStr V r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm

  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext x
    have := RingHom.congr_fun h' (e x)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
    exact RingHom.congr_fun h0 r
  · have hv : ∀ i : Fin 2, g₁ (e.symm (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
        g₂ (e.symm (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
      rw [Fin.forall_fin_two, h0', h1']
      exact ⟨hx, hz⟩
    intro i
    (first | exact hv i | simpa [RingHom.comp_apply] using hv i | (have h__ := hv i; simp [RingHom.comp_apply] at h__; exact h__))

theorem kwYChartEval_mk_one {T : Type} [CommRing T] (W : WeierstrassCurve T) (i : Fin 3) (hi : i ≠ 1)
    (h : coord W.toProjective i ∈ projModelGradingCR W.toProjective (1 • 1)) :
    kwYChartEval T W (Away.mk (projModelGradingCR W.toProjective) (coord_mem W.toProjective 1) 1 (coord W.toProjective i) h) = 0 := by
  simp only [kwYChartEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk']
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec, mul_zero]
  show (MvPolynomial.eval ![(0 : T), 1, 0]) (MvPolynomial.X i) = 0
  fin_cases i <;> simp at hi ⊢

theorem kwYChartEval_xOverY {T : Type} [CommRing T] (W : WeierstrassCurve T) :
    kwYChartEval T W (xOverY W.toProjective) = 0 :=
  kwYChartEval_mk_one W 0 (by decide) _

theorem kwYChartEval_zOverY {T : Type} [CommRing T] (W : WeierstrassCurve T) :
    kwYChartEval T W (zOverY W.toProjective) = 0 :=
  kwYChartEval_mk_one W 2 (by decide) _

theorem kwYChartEval_comp_originStr {T : Type} [CommRing T] (W : WeierstrassCurve T) :
    (kwYChartEval T W).comp (originStr W.toProjective) = RingHom.id T :=
  kwYChartEval_section T W

theorem kwZeroSect_eq {T : Type} [CommRing T] (W : WeierstrassCurve T) :
    (kwZeroSect T W).1 = Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := rfl

theorem originChartι_comp_projModelStrCR {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T) :
    originChartι V ≫ projModelStrCR V = Spec.map (CommRingCat.ofHom (originStr V)) := by
  rw [projModelStrCR, ← Category.assoc]
  erw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  rfl

end originext

section origin

variable {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T)

def originEv : MvPolynomial (Fin 2) T →+* OriginChartRing V :=
  MvPolynomial.eval₂Hom (originStr V) ![xOverY V, zOverY V]

theorem originEv_C (r : T) : originEv V (MvPolynomial.C r) = originStr V r := by
  simp [originEv]

theorem originEv_X (i : Fin 2) : originEv V (MvPolynomial.X i) = ![xOverY V, zOverY V] i := by
  simp [originEv]

theorem originEv_surjective : Function.Surjective (originEv V) := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij

  have key : (e.symm.toRingHom).comp (Ideal.Quotient.mk _) = originEv V := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, originEv_C]
      apply e.injective
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
      exact (RingHom.congr_fun hcomp r).symm
    · intro i
      rw [RingHom.comp_apply, originEv_X]
      apply e.injective
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
      fin_cases i
      · have := hmk 1 (MvPolynomial.X 0)
          ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
        simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
        exact this.symm
      · have := hmk 1 (MvPolynomial.X 2)
          ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 2))
        simp only [MvPolynomial.aeval_X, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
        exact this.symm
  rw [← key]
  exact e.symm.surjective.comp Ideal.Quotient.mk_surjective

theorem originStr_injective (W : WeierstrassCurve T) : Function.Injective (originStr W.toProjective) := by
  intro a b h
  have := congrArg (kwYChartEval T W) h
  rwa [← RingHom.comp_apply, ← RingHom.comp_apply, kwYChartEval_comp_originStr] at this

theorem charP_originChartRing (q : ℕ) [CharP T q] (W : WeierstrassCurve T) : CharP (OriginChartRing W.toProjective) q :=
  charP_of_injective_ringHom (originStr_injective W) q

theorem finitePresentation_originStr : (originStr V).FinitePresentation := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing V
  letI : Algebra T (OriginChartRing V) := (originStr V).toAlgebra
  let e := RingEquiv.ofBijective f hbij
  let e' : OriginChartRing V ≃ₐ[T] _ := AlgEquiv.ofRingEquiv (f := e) (fun t => RingHom.congr_fun hcomp t)
  haveI : Algebra.FinitePresentation T (MvPolynomial (Fin 2) T ⧸ Ideal.span (Set.range fun _ : Fin 1 =>
      MvPolynomial.aeval (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) T) V.polynomial)) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  exact Algebra.FinitePresentation.equiv e'.symm

end origin

end RelFrobAlg

namespace RelFrobAlg

section psiY

variable (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [CharP T q] (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective)
    (hx : ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q)
    (hz : ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q)
    (hcomp : originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)

include hΦ hcomp in

theorem psiY_comp_originStr :
    ψ.comp (originStr (W.map (frobenius T q)).toProjective) = originStr W.toProjective := by
  have h1 : Spec.map (CommRingCat.ofHom (originStr W.toProjective)) =
      Spec.map (CommRingCat.ofHom (ψ.comp (originStr (W.map (frobenius T q)).toProjective))) := by
    rw [← originChartι_comp_projModelStrCR, ← hΦ, ← Category.assoc, hcomp, Category.assoc,
      originChartι_comp_projModelStrCR, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 := Spec.map_inj.mp h1
  exact (congrArg CommRingCat.Hom.hom h2).symm

include hΦ hx hz hcomp in

theorem pow_mem_range_psiY (b : OriginChartRing W.toProjective) : ∃ a, ψ a = b ^ q := by
  haveI := charP_originChartRing q W
  have hlin := psiY_comp_originStr q T W Φ hΦ ψ hcomp
  let S : Subring (OriginChartRing W.toProjective) := (ψ.range).comap (frobenius (OriginChartRing W.toProjective) q)
  have hS : ∀ P : MvPolynomial (Fin 2) T, originEv W.toProjective P ∈ S := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C r =>
      rw [originEv_C]
      show frobenius _ q (originStr W.toProjective r) ∈ ψ.range
      refine ⟨originStr (W.map (frobenius T q)).toProjective (r ^ q), ?_⟩
      rw [frobenius_def, ← map_pow, ← hlin]; rfl
    | add p₁ p₂ h₁ h₂ => rw [map_add]; exact S.add_mem h₁ h₂
    | mul_X p i hp =>
      rw [map_mul, originEv_X]
      refine S.mul_mem hp ?_
      show frobenius _ q (![xOverY W.toProjective, zOverY W.toProjective] i) ∈ ψ.range
      fin_cases i
      · exact ⟨xOverY (W.map (frobenius T q)).toProjective, by rw [hx, frobenius_def]; rfl⟩
      · exact ⟨zOverY (W.map (frobenius T q)).toProjective, by rw [hz, frobenius_def]; rfl⟩
  obtain ⟨P, rfl⟩ := originEv_surjective W.toProjective b
  obtain ⟨a, ha⟩ := (Subring.mem_comap.mp (hS P))
  exact ⟨a, by rw [ha, frobenius_def]⟩

include hΦ hx hz hcomp in

theorem isNilpotent_of_psiY_eq_zero (a : OriginChartRing (W.map (frobenius T q)).toProjective) (ha : ψ a = 0) :
    IsNilpotent a := by
  haveI hB := charP_originChartRing q (W.map (frobenius T q))
  have hlin := psiY_comp_originStr q T W Φ hΦ ψ hcomp

  have hrel : zOverY (W.map (frobenius T q)).toProjective +
      originStr (W.map (frobenius T q)).toProjective ((W.map (frobenius T q)).a₁) * xOverY (W.map (frobenius T q)).toProjective *
        zOverY (W.map (frobenius T q)).toProjective +
      originStr (W.map (frobenius T q)).toProjective ((W.map (frobenius T q)).a₃) * zOverY (W.map (frobenius T q)).toProjective ^ 2 =
      xOverY (W.map (frobenius T q)).toProjective ^ 3 +
      originStr (W.map (frobenius T q)).toProjective ((W.map (frobenius T q)).a₂) * xOverY (W.map (frobenius T q)).toProjective ^ 2 *
        zOverY (W.map (frobenius T q)).toProjective +
      originStr (W.map (frobenius T q)).toProjective ((W.map (frobenius T q)).a₄) * xOverY (W.map (frobenius T q)).toProjective *
        zOverY (W.map (frobenius T q)).toProjective ^ 2 +
      originStr (W.map (frobenius T q)).toProjective ((W.map (frobenius T q)).a₆) * zOverY (W.map (frobenius T q)).toProjective ^ 3 := by
    letI : Algebra T (OriginChartRing (W.map (frobenius T q)).toProjective) :=
      (originStr (W.map (frobenius T q)).toProjective).toAlgebra
    have := WeierstrassCurve.DrinfeldGlobal.originChart_rel (W.map (frobenius T q)) (RingHom.id _) (fun t => rfl)
    (first | exact this | simpa only [RingHom.id_apply] using this | (have h__ := this; simp only [RingHom.id_apply] at h__; exact h__))

  obtain ⟨γ, hγs, hγx, hγz⟩ : ∃ γ : OriginChartRing W.toProjective →+* OriginChartRing (W.map (frobenius T q)).toProjective,
      (∀ t : T, γ (originStr W.toProjective t) = originStr (W.map (frobenius T q)).toProjective (t ^ q)) ∧
      γ (xOverY W.toProjective) = xOverY (W.map (frobenius T q)).toProjective ∧
      γ (zOverY W.toProjective) = zOverY (W.map (frobenius T q)).toProjective := by
    letI : Algebra T (OriginChartRing (W.map (frobenius T q)).toProjective) :=
      ((originStr (W.map (frobenius T q)).toProjective).comp (frobenius T q)).toAlgebra
    obtain ⟨γ, hγs, hγx, hγz⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_eq W
      (xOverY (W.map (frobenius T q)).toProjective) (zOverY (W.map (frobenius T q)).toProjective) (by
        simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, frobenius_def]
        simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
          WeierstrassCurve.map_a₆, frobenius_def] using hrel)
    refine ⟨γ, fun t => ?_, hγx, hγz⟩
    have := hγs t
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, frobenius_def] at this
    exact this

  have hγψ : γ.comp ψ = frobenius (OriginChartRing (W.map (frobenius T q)).toProjective) q := by
    apply originChart_ringHom_ext
    · ext t
      simp only [RingHom.comp_apply, frobenius_def]
      rw [← map_pow, ← RingHom.comp_apply ψ, hlin, hγs]
    · rw [RingHom.comp_apply, hx, map_pow, hγx, frobenius_def]
    · rw [RingHom.comp_apply, hz, map_pow, hγz, frobenius_def]
  refine ⟨q, ?_⟩
  have := RingHom.congr_fun hγψ a
  rw [RingHom.comp_apply, ha, map_zero, frobenius_def] at this
  exact this.symm

include hΦ hcomp in
theorem finitePresentation_psiY : ψ.FinitePresentation := by
  have hlin := psiY_comp_originStr q T W Φ hΦ ψ hcomp
  refine RingHom.FinitePresentation.of_comp_finiteType (originStr (W.map (frobenius T q)).toProjective) ?_ ?_
  · rw [hlin]; exact finitePresentation_originStr _
  · exact RingHom.FiniteType.of_finitePresentation (finitePresentation_originStr _)

include hΦ hx hz hcomp in
theorem finite_psiY : ψ.Finite :=
  RingHom.IsIntegral.to_finite
    (isIntegral_of_pow_mem_range ψ q (Fact.out : q.Prime).pos (pow_mem_range_psiY q T W Φ hΦ ψ hx hz hcomp))
    (RingHom.FiniteType.of_finitePresentation (finitePresentation_psiY q T W Φ hΦ ψ hcomp))

include hΦ hx hz hcomp in
theorem surjective_specMap_psiY : Function.Surjective (Spec.map (CommRingCat.ofHom ψ)).base :=
  surjective_specMap_base_of_isIntegral_of_ker_le_nilradical ψ
    (isIntegral_of_pow_mem_range ψ q (Fact.out : q.Prime).pos (pow_mem_range_psiY q T W Φ hΦ ψ hx hz hcomp))
    (isNilpotent_of_psiY_eq_zero q T W Φ hΦ ψ hx hz hcomp)

end psiY

end RelFrobAlg

namespace F1bAux

open MvPolynomial TopologicalSpace

section Cover

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

theorem polynomial_add_X0_cube :
    V.polynomial + X 0 ^ 3 = X 2 * (X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
      - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    show (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 0)) ^ 3 ∈ _
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem iSup_chartRange_eq_top :
    (⨆ b : Bool, cond b (zChartι V).opensRange (originChartι V).opensRange) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Opens.mem_iSup]
  by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
  · refine ⟨true, ?_⟩
    show x ∈ (zChartι V).opensRange
    rw [Proj.opensRange_awayι, Proj.mem_basicOpen]
    exact fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
  · refine ⟨false, ?_⟩
    show x ∈ (originChartι V).opensRange
    rw [Proj.opensRange_awayι, Proj.mem_basicOpen]
    exact h1

end Cover

end F1bAux

end

theorem solution
    (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [CharP T q]
    (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective) :
    LocallyQuasiFinite Φ := by
  obtain ⟨ψZ, hZx, hZy, hZc⟩ := hZ
  obtain ⟨ψY, hYx, hYz, hYc⟩ := hY
  have finZ : ψZ.Finite := RelFrob.finite_psiZ q T W Φ hΦ ψZ hZx hZy hZc
  have finY : ψY.Finite := RelFrobAlg.finite_psiY q T W Φ hΦ ψY hYx hYz hYc
  haveI : IsFinite (Spec.map (CommRingCat.ofHom ψZ)) := (IsFinite.SpecMap_iff _).mpr finZ
  haveI : IsFinite (Spec.map (CommRingCat.ofHom ψY)) := (IsFinite.SpecMap_iff _).mpr finY
  have hZ' : LocallyQuasiFinite (zChartι W.toProjective ≫ Φ) := by rw [hZc]; infer_instance
  have hY' : LocallyQuasiFinite (originChartι W.toProjective ≫ Φ) := by rw [hYc]; infer_instance
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyQuasiFinite) _
    (F1bAux.iSup_chartRange_eq_top W.toProjective)
  intro b
  cases b
  · show LocallyQuasiFinite ((originChartι W.toProjective).opensRange.ι ≫ Φ)
    have e : (originChartι W.toProjective).opensRange.ι =
        (originChartι W.toProjective).isoOpensRange.inv ≫ originChartι W.toProjective :=
      (Iso.eq_inv_comp _).mpr (Scheme.Hom.isoOpensRange_hom_ι _)
    rw [e, Category.assoc]
    infer_instance
  · show LocallyQuasiFinite ((zChartι W.toProjective).opensRange.ι ≫ Φ)
    have e : (zChartι W.toProjective).opensRange.ι =
        (zChartι W.toProjective).isoOpensRange.inv ≫ zChartι W.toProjective :=
      (Iso.eq_inv_comp _).mpr (Scheme.Hom.isoOpensRange_hom_ι _)
    rw [e, Category.assoc]
    infer_instance

end S_WeierstrassCurve_DrinfeldGlobal_locallyQuasiFinite_of_zChart_pow_originChart_pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_locallyQuasiFinite_of_zChart_pow_originChart_pow (solution)

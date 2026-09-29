-- Prove2me | solution 1 for WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c2fb065c-feb4-58f6-9818-ebce0ed313df

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassProjModel_kwYChartEval_gen_eq
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

set_option maxHeartbeats 12800000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped WeierstrassCurve.Projective

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR projModelCR projModelStrCR IsPointsEval kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrChart_dehom_polynomial kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwYChartEval kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kwYChartEval_gen_eq exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain exists_isCoefficientHom RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel NeronModelInfra"

attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

theorem kwLRAffinePtSetEquiv_axiomAnchor : True :=
  have _h₁ : True = True := propext Iff.rfl
  have _h₂ : ℕ := Classical.choice ⟨0⟩
  have _h₃ : Quot.mk (fun (_ _ : ℕ) => True) 0 = Quot.mk (fun (_ _ : ℕ) => True) 1 :=
    Quot.sound trivial
  trivial

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover
set_option quotPrecheck false in
local notation "gen" => kw_lrChart_gen W
set_option quotPrecheck false in
local notation "dehom" => kw_lrChart_dehom W
set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F

set_option quotPrecheck false in
local notation "awayι₃" i => Proj.awayι (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R)) (kw_pbac_mk_X_mem_one_CR R W.toProjective i) one_pos

set_option quotPrecheck false in
local notation "W_F" => kw_lrApt_WF W F

theorem kw_lrApt_coverE_f (i : Fin 3) :
    (coverE).f i = Proj.awayι (projModelGradingCR W.toProjective)
      (mk₃ (X i : MvPolynomial (Fin 3) R)) (kw_pbac_mk_X_mem_one_CR R W.toProjective i) one_pos :=
  rfl

theorem kw_lrApt_coverE_f_comp_π (i : Fin 3) :
    (coverE).f i ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) :=
  kw_pbac_awayι_comp_projModelStrCR R W.toProjective i

namespace ProjWeierstrassDehomog

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

theorem eq_smul_pointAtInfinity [NoZeroDivisors R]
    {V : WeierstrassCurve.Projective R} {P : Fin 3 → R}
    (hP : eval P V.polynomial = 0) (hPz : P 2 = 0) :
    P = P 1 • ![0, 1, 0] := by
  have hx : P 0 = 0 := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero (W' := V) hP hPz
  funext i
  fin_cases i <;>
    simp [hx, hPz, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]

open scoped WeierstrassCurve.Projective in

theorem pointClass_eq_pointAtInfinity {F : Type*} [Field F]
    {V : WeierstrassCurve.Projective F} {P : Fin 3 → F}
    (hP : eval P V.polynomial = 0) (hPz : P 2 = 0) (hP0 : P ≠ 0) :
    (⟦P⟧ : WeierstrassCurve.Projective.PointClass F) = ⟦![0, 1, 0]⟧ := by
  have hx : P 0 = 0 := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero (W' := V) hP hPz
  have hy : P 1 ≠ 0 := by
    intro hy
    exact hP0 (by funext i; fin_cases i <;> assumption)
  refine Quotient.sound ⟨Units.mk0 (P 1) hy, ?_⟩
  funext i
  fin_cases i <;>
    simp [hx, hPz, Units.smul_def, Pi.smul_apply, smul_eq_mul]

end PointDictionary

end ProjWeierstrassDehomog

section ChartClassification

theorem kw_lrApt_gen_self (i : Fin 3) : gen i i = 1 := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  refine HomogeneousLocalization.val_injective _ ?_
  rw [kw_lrChart_gen_val, HomogeneousLocalization.val_one]
  exact Localization.mk_self
    (⟨mk₃ (X i : MvPolynomial (Fin 3) R), 1, pow_one _⟩ : Submonoid.powers _)

theorem kw_lrApt_chartEval_self (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    kw_lrApt_chartEval W F i ψ i = 1 := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  unfold kw_lrApt_chartEval
  rw [kw_lrApt_gen_self W i, map_one]

theorem kw_lrApt_chartEval_ne_zero (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    kw_lrApt_chartEval W F i ψ ≠ 0 := by
  intro h
  exact one_ne_zero ((kw_lrApt_chartEval_self W F i ψ).symm.trans (congr_fun h i))

theorem kw_lrApt_aeval_chartEval (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    (aeval (kw_lrApt_chartEval W F i ψ) : MvPolynomial (Fin 3) R →ₐ[R] F)
      = ψ.comp (dehom i) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  show aeval _ (X m) = ψ (aeval _ (X m))
  rw [aeval_X, aeval_X]; rfl

theorem kw_lrApt_eval_chartEval (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F)
    (p : MvPolynomial (Fin 3) R) :
    eval (kw_lrApt_chartEval W F i ψ) (MvPolynomial.map (algebraMap R F) p) = ψ (dehom i p) := by
  have h := congr_fun (congr_arg DFunLike.coe (kw_lrApt_aeval_chartEval W F i ψ)) p
  rw [AlgHom.comp_apply] at h
  rw [MvPolynomial.eval_map, ← aeval_def, h]

theorem kw_lrApt_chartEval_equation (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    (W_F).Equation (kw_lrApt_chartEval W F i ψ) := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor

  show eval _ (W_F).polynomial = 0
  rw [show (W_F).polynomial = MvPolynomial.map (algebraMap R F) W.toProjective.polynomial
        from Projective.map_polynomial (W' := W.toProjective) (f := algebraMap R F),
    kw_lrApt_eval_chartEval W F i ψ, kw_lrChart_dehom_polynomial W i, map_zero]

noncomputable def kw_lrApt_evalℬ (P : Fin 3 → F) (hP : (W_F).Equation P) :
    ProjModelRingCR W.toProjective →+* F :=
  Ideal.Quotient.lift _ (MvPolynomial.aeval P).toRingHom fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_def, ← MvPolynomial.eval_map]
    exact (Projective.map_polynomial (W' := W.toProjective) (f := algebraMap R F)).symm ▸ hP

theorem kw_lrApt_evalℬ_mk_X (P : Fin 3 → F) (hP : (W_F).Equation P) (m : Fin 3) :
    kw_lrApt_evalℬ W F P hP (mk₃ (X m : MvPolynomial (Fin 3) R)) = P m :=
  aeval_X _ _

theorem kw_lrApt_evalℬ_comp_algebraMap (P : Fin 3 → F) (hP : (W_F).Equation P) :
    (kw_lrApt_evalℬ W F P hP).comp (algebraMap R (ProjModelRingCR W.toProjective))
      = algebraMap R F :=
  RingHom.ext fun _ => aeval_C _ _

theorem kw_lrApt_dehom_surjective (i : Fin 3) :
    Function.Surjective (kw_lrChart_dehom W i) := fun x => by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W i) x
  have ha' : a ∈ projModelGradingCR W.toProjective n := by simpa using ha
  obtain ⟨p, hpmem, hpeq⟩ := (mem_quotGradingSubmodule_iff _ _).mp ha'
  refine ⟨p, ?_⟩
  rw [kw_lrChart_dehom_isHomogeneous W i n p ((mem_homogeneousSubmodule _ _).mp hpmem)]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, hpeq]

noncomputable def kw_lrApt_ofVecRingHom (i : Fin 3) (P : Fin 3 → F)
    (hP : (W_F).Equation P) (hPi : P i = 1) : (𝒜 i) →+* F :=
  (IsLocalization.Away.lift (g := kw_lrApt_evalℬ W F P hP)
      (mk₃ (X i : MvPolynomial (Fin 3) R))
      ((kw_lrApt_evalℬ_mk_X W F P hP i).symm ▸ hPi ▸ isUnit_one)).comp
    (algebraMap (𝒜 i)
      (Localization.Away (mk₃ (X i : MvPolynomial (Fin 3) R))))

theorem kw_lrApt_ofVecRingHom_comp_algebraMap (i : Fin 3) (P : Fin 3 → F)
    (hP : (W_F).Equation P) (hPi : P i = 1) :
    (kw_lrApt_ofVecRingHom W F i P hP hPi).comp (algebraMap R (𝒜 i)) = algebraMap R F := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, kw_lrApt_ofVecRingHom,
    HomogeneousLocalization.algebraMap_apply]
  have hval :
      (algebraMap R (𝒜 i) r).val
        = algebraMap (ProjModelRingCR W.toProjective)
            (Localization.Away (mk₃ (X i : MvPolynomial (Fin 3) R)))
            (algebraMap R (ProjModelRingCR W.toProjective) r) := rfl
  rw [hval, IsLocalization.Away.lift, IsLocalization.lift_eq]
  exact RingHom.congr_fun (kw_lrApt_evalℬ_comp_algebraMap W F P hP) r

noncomputable def kw_lrApt_ofVec (i : Fin 3) (P : Fin 3 → F)
    (hP : (W_F).Equation P) (hPi : P i = 1) : (𝒜 i) →ₐ[R] F :=
  { kw_lrApt_ofVecRingHom W F i P hP hPi with
    commutes' := RingHom.congr_fun (kw_lrApt_ofVecRingHom_comp_algebraMap W F i P hP hPi) }

theorem kw_lrApt_ofVec_gen (i : Fin 3) (P : Fin 3 → F)
    (hP : (W_F).Equation P) (hPi : P i = 1) (m : Fin 3) :
    kw_lrApt_ofVec W F i P hP hPi (gen i m) = P m := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor

  show kw_lrApt_ofVecRingHom W F i P hP hPi (gen i m) = P m
  unfold kw_lrApt_ofVecRingHom
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  have hden : (gen i m).val * algebraMap (ProjModelRingCR W.toProjective)
      (Localization.Away (mk₃ (X i : MvPolynomial (Fin 3) R)))
      (mk₃ (X i : MvPolynomial (Fin 3) R))
      = algebraMap _ _ (mk₃ (X m : MvPolynomial (Fin 3) R)) := by
    rw [kw_lrChart_gen_val, ← Localization.mk_one_eq_algebraMap,
      ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by push_cast; ring⟩
  have hu := (kw_lrApt_evalℬ_mk_X W F P hP i).symm ▸ hPi ▸ isUnit_one
  have hlift := congrArg
    (IsLocalization.Away.lift (g := kw_lrApt_evalℬ W F P hP)
      (mk₃ (X i : MvPolynomial (Fin 3) R)) hu) hden
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq,
    kw_lrApt_evalℬ_mk_X, kw_lrApt_evalℬ_mk_X, hPi, mul_one] at hlift
  exact hlift

theorem kw_lrApt_chartEval_ofVec (i : Fin 3) (P : Fin 3 → F)
    (hP : (W_F).Equation P) (hPi : P i = 1) :
    kw_lrApt_chartEval W F i (kw_lrApt_ofVec W F i P hP hPi) = P :=
  funext fun m => kw_lrApt_ofVec_gen W F i P hP hPi m

theorem kw_lrApt_chartEval_injective (i : Fin 3) :
    Function.Injective (kw_lrApt_chartEval W F i) := fun ψ ψ' h => by
  have hd : ψ.comp (dehom i) = ψ'.comp (dehom i) := by
    rw [← kw_lrApt_aeval_chartEval, ← kw_lrApt_aeval_chartEval, h]
  exact AlgHom.ext fun x => by
    obtain ⟨p, rfl⟩ := kw_lrApt_dehom_surjective W i x
    exact AlgHom.congr_fun hd p

theorem kw_lrApt_ofVec_chartEval (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    kw_lrApt_ofVec W F i (kw_lrApt_chartEval W F i ψ)
      (kw_lrApt_chartEval_equation W F i ψ) (kw_lrApt_chartEval_self W F i ψ) = ψ := by

  have h1 := kw_lrApt_aeval_chartEval W F i
    (kw_lrApt_ofVec W F i (kw_lrApt_chartEval W F i ψ)
      (kw_lrApt_chartEval_equation W F i ψ) (kw_lrApt_chartEval_self W F i ψ))
  rw [kw_lrApt_chartEval_ofVec, kw_lrApt_aeval_chartEval W F i ψ] at h1
  exact AlgHom.ext fun x => by
    obtain ⟨p, rfl⟩ := kw_lrApt_dehom_surjective W i x
    exact (AlgHom.congr_fun h1 p).symm

end ChartClassification

section ChartFactorization

theorem kw_lrApt_factor_of_range (φ : SchemeHomOver (t_F) π) (i : Fin 3)
    (hrange : Set.range φ.1 ⊆ Set.range (awayι₃ i)) :
    ∃ ψ : (𝒜 i) →ₐ[R] F,
      φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (coverE).f i := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  let g : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (𝒜 i)) :=
    IsOpenImmersion.lift (awayι₃ i) φ.1 hrange
  have hgfac : g ≫ (coverE).f i = φ.1 := IsOpenImmersion.lift_fac (awayι₃ i) φ.1 hrange
  let ρ : CommRingCat.of (𝒜 i) ⟶ CommRingCat.of F := Spec.preimage g
  have hρ : Spec.map ρ = g := Spec.map_preimage g
  have hspec : Spec.map (CommRingCat.ofHom (ρ.hom.comp (algebraMap R (𝒜 i))))
      = Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hρ,
      ← kw_lrApt_coverE_f_comp_π W i]

    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (projModelStrCR W.toProjective)) hgfac).trans φ.2)
  have hcomm : ρ.hom.comp (algebraMap R (𝒜 i)) = algebraMap R F :=
    CommRingCat.hom_ext_iff.mp (Spec.map_injective hspec)
  exact ⟨⟨ρ.hom, RingHom.congr_fun hcomm⟩,
    by rw [show (⟨ρ.hom, RingHom.congr_fun hcomm⟩ : (𝒜 i) →ₐ[R] F).toRingHom = ρ.hom from rfl,
        CommRingCat.ofHom_hom, hρ, hgfac]⟩

theorem kw_lrApt_schemeHom_factor (φ : SchemeHomOver (t_F) π) :
    ∃ (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F),
      φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (coverE).f i := by

  let pt : ↑(Spec (CommRingCat.of F)) := default
  let i := (coverE).idx (φ.1.base pt)
  have hrange : Set.range φ.1 ⊆ Set.range (awayι₃ i) := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q pt]
    exact (coverE).covers (φ.1.base pt)
  exact ⟨i, kw_lrApt_factor_of_range W F φ i hrange⟩

noncomputable def kw_lrApt_chartIdx (φ : SchemeHomOver (t_F) π) : Fin 3 :=
  (kw_lrApt_schemeHom_factor W F φ).choose

noncomputable def kw_lrApt_chartHom (φ : SchemeHomOver (t_F) π) :
    (𝒜 (kw_lrApt_chartIdx W F φ)) →ₐ[R] F :=
  (kw_lrApt_schemeHom_factor W F φ).choose_spec.choose

theorem kw_lrApt_chartHom_fac (φ : SchemeHomOver (t_F) π) :
    φ.1 = Spec.map (CommRingCat.ofHom (kw_lrApt_chartHom W F φ).toRingHom)
            ≫ (coverE).f (kw_lrApt_chartIdx W F φ) :=
  (kw_lrApt_schemeHom_factor W F φ).choose_spec.choose_spec

theorem kw_lrApt_factor_unique (φ : Spec (CommRingCat.of F) ⟶ E) {i : Fin 3}
    {ψ ψ' : (𝒜 i) →ₐ[R] F}
    (hψ : φ = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (coverE).f i)
    (hψ' : φ = Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫ (coverE).f i) :
    ψ = ψ' := by
  have h := hψ.symm.trans hψ'
  rw [show (coverE).f i = (awayι₃ i) from rfl, cancel_mono] at h
  exact AlgHom.ext (RingHom.congr_fun (CommRingCat.hom_ext_iff.mp (Spec.map_injective h)))

theorem kw_lrApt_gen_eq_awayMk (i m : Fin 3) :
    gen i m = HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
      (kw_lrChart_mkX_mem_one W i) 1 (mk₃ (X m : MvPolynomial (Fin 3) R))
      (kw_lrChart_mk_mem_of_isHomogeneous W 1 (X m) (isHomogeneous_X R m)) := by
  have h := kw_lrChart_dehom_isHomogeneous W i 1 (X m) (isHomogeneous_X R m)
  rw [kw_lrChart_dehom, aeval_X] at h; exact h

theorem kw_lrApt_awayMap_gen_identity (i j m : Fin 3) :
    HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
        (kw_lrChart_mkX_mem_one W i)
        (mul_comm (mk₃ (X i : MvPolynomial (Fin 3) R)) (mk₃ (X j : _))) (gen j m)
      * HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
        (kw_lrChart_mkX_mem_one W j) rfl (gen i j)
      = HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
        (kw_lrChart_mkX_mem_one W j) rfl (gen i m) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul,
    kw_lrApt_gen_eq_awayMk W j m, kw_lrApt_gen_eq_awayMk W i j, kw_lrApt_gen_eq_awayMk W i m,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem kw_lrApt_chartEval_compat {i j : Fin 3}
    {ψᵢ : (𝒜 i) →ₐ[R] F} {ψⱼ : (𝒜 j) →ₐ[R] F}
    (hfac_i : ∃ φ : SchemeHomOver (t_F) π,
      φ.1 = Spec.map (CommRingCat.ofHom ψᵢ.toRingHom) ≫ (coverE).f i ∧
      φ.1 = Spec.map (CommRingCat.ofHom ψⱼ.toRingHom) ≫ (coverE).f j) :
    (⟦kw_lrApt_chartEval W F i ψᵢ⟧ : Projective.PointClass F)
      = ⟦kw_lrApt_chartEval W F j ψⱼ⟧ := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  obtain ⟨φ, hφi, hφj⟩ := hfac_i

  have hmem : mk₃ (X i : MvPolynomial (Fin 3) R) * mk₃ (X j : _)
      ∈ projModelGradingCR W.toProjective (1 + 1) :=
    SetLike.mul_mem_graded (kw_lrChart_mkX_mem_one W i) (kw_lrChart_mkX_mem_one W j)
  have hrange : Set.range φ.1 ⊆ Set.range (Proj.awayι (projModelGradingCR W.toProjective)
      (mk₃ (X i : MvPolynomial (Fin 3) R) * mk₃ (X j : _)) hmem two_pos) := by
    have hcap : (Proj.awayι _ _ hmem two_pos).opensRange
        = (awayι₃ i).opensRange ⊓ (awayι₃ j).opensRange := by
      rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.opensRange_awayι,
        ← Proj.basicOpen_mul]
    intro x hx
    rw [← Scheme.Hom.coe_opensRange, hcap]
    exact ⟨(Set.range_comp_subset_range _ _) (hφi ▸ hx),
      (Set.range_comp_subset_range _ _) (hφj ▸ hx)⟩

  let g := IsOpenImmersion.lift _ φ.1 hrange
  have hgfac : g ≫ _ = φ.1 := IsOpenImmersion.lift_fac _ _ hrange
  let χ := Spec.preimage g
  have hχ : Spec.map χ = g := Spec.map_preimage g

  have hcompᵢ : χ.hom.comp (HomogeneousLocalization.awayMap
        (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W j) rfl)
      = ψᵢ.toRingHom := by
    have hs : Spec.map (CommRingCat.ofHom ψᵢ.toRingHom)
        = Spec.map (CommRingCat.ofHom (χ.hom.comp (HomogeneousLocalization.awayMap _
            (kw_lrChart_mkX_mem_one W j) rfl))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hχ,
        ← cancel_mono (awayι₃ i), Category.assoc, Proj.SpecMap_awayMap_awayι, hgfac, hφi]; rfl
    exact (CommRingCat.hom_ext_iff.mp (Spec.map_injective hs)).symm
  have hcompⱼ : χ.hom.comp (HomogeneousLocalization.awayMap
        (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W i) (mul_comm _ _))
      = ψⱼ.toRingHom := by
    have hs : Spec.map (CommRingCat.ofHom ψⱼ.toRingHom)
        = Spec.map (CommRingCat.ofHom (χ.hom.comp (HomogeneousLocalization.awayMap _
            (kw_lrChart_mkX_mem_one W i) (mul_comm _ _)))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hχ,
        ← cancel_mono (awayι₃ j), Category.assoc, Proj.SpecMap_awayMap_awayι, hgfac, hφj]; rfl
    exact (CommRingCat.hom_ext_iff.mp (Spec.map_injective hs)).symm

  have hχᵢ : ∀ a, χ.hom (HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
      (kw_lrChart_mkX_mem_one W j) rfl a) = ψᵢ a :=
    fun a => RingHom.congr_fun hcompᵢ a
  have hχⱼ : ∀ a, χ.hom (HomogeneousLocalization.awayMap (projModelGradingCR W.toProjective)
      (kw_lrChart_mkX_mem_one W i) (mul_comm _ _) a) = ψⱼ a :=
    fun a => RingHom.congr_fun hcompⱼ a
  have hprop : ∀ m, kw_lrApt_chartEval W F j ψⱼ m * kw_lrApt_chartEval W F i ψᵢ j
      = kw_lrApt_chartEval W F i ψᵢ m := fun m => by
    have hid := congrArg χ.hom (kw_lrApt_awayMap_gen_identity W i j m)
    rw [map_mul, hχⱼ, hχᵢ, hχᵢ] at hid
    exact hid

  have hunit : IsUnit (kw_lrApt_chartEval W F i ψᵢ j) := by
    refine isUnit_iff_ne_zero.mpr fun hz => ?_
    have h := hprop i; rw [hz, mul_zero, kw_lrApt_chartEval_self] at h
    exact one_ne_zero h.symm
  rw [show kw_lrApt_chartEval W F i ψᵢ
      = (kw_lrApt_chartEval W F i ψᵢ j) • kw_lrApt_chartEval W F j ψⱼ
      from funext fun m => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hprop m]]
  exact Projective.smul_eq _ hunit

end ChartFactorization

section Forward

noncomputable def kw_lrApt_toVec (φ : SchemeHomOver (t_F) π) : Fin 3 → F :=
  kw_lrApt_chartEval W F (kw_lrApt_chartIdx W F φ) (kw_lrApt_chartHom W F φ)

theorem kw_lrApt_toVec_equation (φ : SchemeHomOver (t_F) π) :
    (W_F).Equation (kw_lrApt_toVec W F φ) :=
  kw_lrApt_chartEval_equation W F _ _

theorem kw_lrApt_toVec_ne_zero (φ : SchemeHomOver (t_F) π) :
    kw_lrApt_toVec W F φ ≠ 0 :=
  kw_lrApt_chartEval_ne_zero W F _ _

noncomputable def kw_lrApt_toPointClass (φ : SchemeHomOver (t_F) π) :
    Projective.PointClass F :=
  ⟦kw_lrApt_toVec W F φ⟧

theorem kw_lrApt_toPointClass_eq_of_fac (φ : SchemeHomOver (t_F) π) (i : Fin 3)
    (ψ : (𝒜 i) →ₐ[R] F)
    (hfac : φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (coverE).f i) :
    kw_lrApt_toPointClass W F φ = ⟦kw_lrApt_chartEval W F i ψ⟧ := by
  exact kw_lrApt_chartEval_compat W F
    ⟨φ, kw_lrApt_chartHom_fac W F φ, hfac⟩

end Forward

section Nonsingular

theorem kw_lrApt_WF_Δ : (W.baseChange F).Δ = algebraMap R F W.Δ := W.map_Δ _

variable {F}

theorem kw_lrApt_nonsingular_of_equation_of_ne_zero (hΔ : algebraMap R F W.Δ ≠ 0)
    {P : Fin 3 → F} (hP : (W_F).Equation P) (hne : P ≠ 0) : (W_F).Nonsingular P := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  have hP' : eval P (W_F).polynomial = 0 := hP
  by_cases hPz : P 2 = 0
  ·

    obtain ⟨_hPx, hPy⟩ :=
      ProjWeierstrassDehomog.X_eq_zero_and_Y_ne_zero_of_Z_eq_zero (V := W_F) hP' hPz hne
    have hsmul := ProjWeierstrassDehomog.eq_smul_pointAtInfinity (V := W_F) hP' hPz
    rw [hsmul]
    exact (Projective.nonsingular_smul _ (isUnit_iff_ne_zero.mpr hPy)).mpr
      Projective.nonsingular_zero
  ·
    refine (Projective.nonsingular_of_Z_ne_zero hPz).mpr ?_
    refine (Affine.equation_iff_nonsingular_of_Δ_ne_zero ?_).mp ?_
    · exact (kw_lrApt_WF_Δ W F).symm ▸ hΔ
    · exact (Projective.equation_of_Z_ne_zero hPz).mp hP

theorem kw_lrApt_nonsingularLift_toPointClass (hΔ : algebraMap R F W.Δ ≠ 0)
    (φ : SchemeHomOver (t_F) π) :
    (W_F).NonsingularLift (kw_lrApt_toPointClass W F φ) :=
  kw_lrApt_nonsingular_of_equation_of_ne_zero W hΔ
    (kw_lrApt_toVec_equation W F φ) (kw_lrApt_toVec_ne_zero W F φ)

end Nonsingular

section Inverse

theorem kw_lrApt_ne_zero_of_nonsingular {P : Fin 3 → F} (hP : (W_F).Nonsingular P) : P ≠ 0 := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  rintro rfl
  rcases hP with ⟨_, hX | hY | hZ⟩
  · exact hX (by rw [Projective.eval_polynomialX]; simp)
  · exact hY (by rw [Projective.eval_polynomialY]; simp)
  · exact hZ (by rw [Projective.eval_polynomialZ]; simp)

variable {W F} in

noncomputable def kw_lrApt_chartOf {P : Fin 3 → F} (hne : P ≠ 0) : Fin 3 :=
  Classical.choose (Function.ne_iff.mp hne)

variable {W F} in
theorem kw_lrApt_chartOf_ne_zero {P : Fin 3 → F} (hne : P ≠ 0) :
    P (kw_lrApt_chartOf hne) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp hne)

noncomputable def kw_lrApt_ofVecScheme {P : Fin 3 → F} (hP : (W_F).Equation P) (hne : P ≠ 0) :
    SchemeHomOver (t_F) π :=
  let i := kw_lrApt_chartOf hne
  let u := (P i)⁻¹
  let P' := u • P
  have hPi' : P' i = 1 := by
    show (P i)⁻¹ * P i = 1
    exact inv_mul_cancel₀ (kw_lrApt_chartOf_ne_zero hne)
  have hP' : (W_F).Equation P' :=
    (Projective.equation_smul P (isUnit_iff_ne_zero.mpr
      (inv_ne_zero (kw_lrApt_chartOf_ne_zero hne)))).mpr hP
  let ψ := kw_lrApt_ofVec W F i P' hP' hPi'
  ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (coverE).f i,
    (Category.assoc _ _ _).trans <|
      (congrArg (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ·)
        (kw_lrApt_coverE_f_comp_π W i)).trans <| by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (Spec.map ∘ CommRingCat.ofHom) ψ.comp_algebraMap⟩

theorem kw_lrApt_eq_of_equiv_of_apply_eq_one {P Q : Fin 3 → F} {i : Fin 3}
    (heq : P ≈ Q) (hPi : P i = 1) (hQi : Q i = 1) : P = Q := by
  obtain ⟨u, hu⟩ := heq
  change u • Q = P at hu
  have hui : u = 1 := by
    refine Units.ext ?_
    have h := congr_fun hu i
    rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, hQi, mul_one] at h
    exact h.trans hPi
  rw [← hu, hui, one_smul]

theorem kw_lrApt_range_subset_of_gen_ne_zero {j : Fin 3} (ψ : (𝒜 j) →ₐ[R] F)
    (i : Fin 3) (hij : ψ (gen j i) ≠ 0) :
    Set.range (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (awayι₃ j))
      ⊆ Set.range (awayι₃ i) := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  have hxrfl : mk₃ (X j : MvPolynomial (Fin 3) R) * mk₃ (X i : MvPolynomial (Fin 3) R)
      = mk₃ (X j : MvPolynomial (Fin 3) R) * mk₃ (X i : MvPolynomial (Fin 3) R) := rfl
  letI := (awayMap (projModelGradingCR W.toProjective)
    (kw_lrChart_mkX_mem_one W i) hxrfl).toAlgebra
  haveI hloc := Away.isLocalization_mul
    (kw_lrChart_mkX_mem_one W j) (kw_lrChart_mkX_mem_one W i) hxrfl one_ne_zero
  have helem : Away.isLocalizationElem
      (kw_lrChart_mkX_mem_one W j) (kw_lrChart_mkX_mem_one W i) = gen j i := by
    rw [kw_lrApt_gen_eq_awayMk]; apply val_injective
    rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by push_cast; ring⟩
  have hunit : IsUnit (ψ.toRingHom (Away.isLocalizationElem
      (kw_lrChart_mkX_mem_one W j) (kw_lrChart_mkX_mem_one W i))) := by
    rw [helem]; exact isUnit_iff_ne_zero.mpr hij
  let χ := IsLocalization.Away.lift (S := Away (projModelGradingCR W.toProjective)
    (mk₃ (X j : MvPolynomial (Fin 3) R) * mk₃ (X i : MvPolynomial (Fin 3) R)))
    (Away.isLocalizationElem (kw_lrChart_mkX_mem_one W j) (kw_lrChart_mkX_mem_one W i)) hunit
  have hfac : ψ.toRingHom = χ.comp (awayMap (projModelGradingCR W.toProjective)
      (kw_lrChart_mkX_mem_one W i) hxrfl) := by
    ext a; symm
    show χ (algebraMap (𝒜 j) _ a) = ψ.toRingHom a
    unfold χ; rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hrefac : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (awayι₃ j)
      = Spec.map (CommRingCat.ofHom
          (χ.comp (awayMap _ (kw_lrChart_mkX_mem_one W j) (mul_comm _ _))))
        ≫ (awayι₃ i) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      Proj.SpecMap_awayMap_awayι,
      ← Proj.SpecMap_awayMap_awayι (g_deg := kw_lrChart_mkX_mem_one W i) (hx := hxrfl),
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hfac]
  rw [hrefac]
  exact fun x hx => Set.range_comp_subset_range _ _ hx

theorem kw_lrApt_toPointClass_ofVecScheme {P : Fin 3 → F} (hP : (W_F).Equation P)
    (hne : P ≠ 0) :
    kw_lrApt_toPointClass W F (kw_lrApt_ofVecScheme W F hP hne) = ⟦P⟧ := by
  set i := kw_lrApt_chartOf hne
  have hPi' : ((P i)⁻¹ • P) i = 1 := inv_mul_cancel₀ (kw_lrApt_chartOf_ne_zero hne)
  have hP' : (W_F).Equation ((P i)⁻¹ • P) :=
    (Projective.equation_smul P (isUnit_iff_ne_zero.mpr
      (inv_ne_zero (kw_lrApt_chartOf_ne_zero hne)))).mpr hP
  have hfac : (kw_lrApt_ofVecScheme W F hP hne).1
      = Spec.map (CommRingCat.ofHom
          (kw_lrApt_ofVec W F i ((P i)⁻¹ • P) hP' hPi').toRingHom) ≫ (coverE).f i := rfl
  rw [kw_lrApt_toPointClass_eq_of_fac W F _ i _ hfac, kw_lrApt_chartEval_ofVec,
    Projective.smul_eq _ (isUnit_iff_ne_zero.mpr (inv_ne_zero (kw_lrApt_chartOf_ne_zero hne)))]

theorem kw_lrApt_toPointClass_injective :
    Function.Injective (kw_lrApt_toPointClass W F) := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  intro φ φ' h
  set i := kw_lrApt_chartIdx W F φ with hi
  set ψ := kw_lrApt_chartHom W F φ with hψ
  have hφfac := kw_lrApt_chartHom_fac W F φ

  obtain ⟨j, ψ', hφ'fac⟩ := kw_lrApt_schemeHom_factor W F φ'

  have hprop : (⟦kw_lrApt_chartEval W F i ψ⟧ : Projective.PointClass F)
      = ⟦kw_lrApt_chartEval W F j ψ'⟧ :=
    (kw_lrApt_toPointClass_eq_of_fac W F φ i ψ hφfac).symm.trans
      (h.trans (kw_lrApt_toPointClass_eq_of_fac W F φ' j ψ' hφ'fac))

  have hψ'i : ψ' (gen j i) ≠ 0 := by
    intro hzero
    obtain ⟨u, hu⟩ := Quotient.eq.mp hprop
    change u • kw_lrApt_chartEval W F j ψ' = kw_lrApt_chartEval W F i ψ at hu
    have h1 := congr_fun hu i
    rw [Pi.smul_apply, show kw_lrApt_chartEval W F j ψ' i = ψ' (gen j i) from rfl,
      hzero, smul_zero, kw_lrApt_chartEval_self] at h1
    exact one_ne_zero h1.symm

  have hrange : Set.range φ'.1 ⊆ Set.range (awayι₃ i) := by
    rw [hφ'fac]; exact kw_lrApt_range_subset_of_gen_ne_zero W F ψ' i hψ'i
  obtain ⟨ψ'', hφ'fac_i⟩ := kw_lrApt_factor_of_range W F φ' i hrange

  have heveq : kw_lrApt_chartEval W F i ψ = kw_lrApt_chartEval W F i ψ'' :=
    kw_lrApt_eq_of_equiv_of_apply_eq_one (F := F)
      (Quotient.eq.mp
        (hprop.trans (kw_lrApt_chartEval_compat W F ⟨φ', hφ'fac, hφ'fac_i⟩)))
      (kw_lrApt_chartEval_self W F i ψ) (kw_lrApt_chartEval_self W F i ψ'')
  have hψeq : ψ = ψ'' := kw_lrApt_chartEval_injective W F i heveq
  exact Subtype.ext (hφfac.trans (hψeq ▸ hφ'fac_i).symm)

theorem kw_lrApt_ofVecScheme_sound {P Q : Fin 3 → F}
    (hP : (W_F).Equation P) (hne : P ≠ 0) (hQ : (W_F).Equation Q) (hne' : Q ≠ 0)
    (heq : (⟦P⟧ : Projective.PointClass F) = ⟦Q⟧) :
    kw_lrApt_ofVecScheme W F hP hne = kw_lrApt_ofVecScheme W F hQ hne' :=
  kw_lrApt_toPointClass_injective W F
    ((kw_lrApt_toPointClass_ofVecScheme W F hP hne).trans
      (heq.trans (kw_lrApt_toPointClass_ofVecScheme W F hQ hne').symm))

noncomputable def kw_lrApt_ofProjPoint (pt : (W_F).Point) : SchemeHomOver (t_F) π := by
  refine pt.point.lift
    (fun P => if h : (W_F).Equation P ∧ P ≠ 0
      then kw_lrApt_ofVecScheme W F h.1 h.2
      else ⟨(t_F) ≫ (kwZeroSect R W).1, by
        rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id]⟩)
    (fun P Q hPQ => ?_)

  beta_reduce
  obtain ⟨u, hu⟩ := hPQ
  change u • Q = P at hu
  have hsmul : (u : F) • Q = P :=
    hu ▸ funext fun k => by rw [Pi.smul_apply, Pi.smul_apply, Units.smul_def]
  subst hsmul
  have hiffE : (W_F).Equation ((u : F) • Q) ↔ (W_F).Equation Q :=
    Projective.equation_smul Q u.isUnit
  have hiff0 : (u : F) • Q ≠ 0 ↔ Q ≠ 0 :=
    ⟨fun h hQ => h (by rw [hQ, smul_zero]),
     fun h hQ => h (funext fun k => by
       have hk := congr_fun hQ k
       rw [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at hk
       exact hk.resolve_left u.ne_zero)⟩
  by_cases hQ : (W_F).Equation Q ∧ Q ≠ 0
  · rw [dif_pos hQ, dif_pos ⟨hiffE.mpr hQ.1, hiff0.mpr hQ.2⟩]
    exact kw_lrApt_ofVecScheme_sound W F _ _ _ _ (Projective.smul_eq Q u.isUnit)
  · rw [dif_neg hQ, dif_neg (fun h => hQ ⟨hiffE.mp h.1, hiff0.mp h.2⟩)]

theorem kw_lrApt_ofProjPoint_mk {P : Fin 3 → F} (hns : (W_F).NonsingularLift ⟦P⟧)
    (hP : (W_F).Equation P) (hne : P ≠ 0) :
    kw_lrApt_ofProjPoint W F ⟨hns⟩ = kw_lrApt_ofVecScheme W F hP hne :=
  dif_pos ⟨hP, hne⟩

end Inverse

section Assembly

variable (hΔ : algebraMap R F W.Δ ≠ 0)

noncomputable def kw_lrApt_toProjPoint (φ : SchemeHomOver (t_F) π) : (W_F).Point :=
  ⟨kw_lrApt_nonsingularLift_toPointClass W hΔ φ⟩

noncomputable def kw_lrApt_projPointEquiv : SchemeHomOver (t_F) π ≃ (W_F).Point where
  toFun := kw_lrApt_toProjPoint W F hΔ
  invFun := kw_lrApt_ofProjPoint W F
  left_inv := fun φ => by
    have hc : (W_F).Equation (kw_lrApt_toVec W F φ) ∧ kw_lrApt_toVec W F φ ≠ 0 :=
      ⟨kw_lrApt_toVec_equation W F φ, kw_lrApt_toVec_ne_zero W F φ⟩
    refine kw_lrApt_toPointClass_injective W F ?_
    rw [show kw_lrApt_ofProjPoint W F (kw_lrApt_toProjPoint W F hΔ φ)
        = kw_lrApt_ofVecScheme W F hc.1 hc.2 from
        kw_lrApt_ofProjPoint_mk W F _ hc.1 hc.2,
      kw_lrApt_toPointClass_ofVecScheme]
    rfl
  right_inv := fun pt => by
    obtain ⟨P, hP⟩ := Quotient.exists_rep pt.point
    have hnsL : (W_F).NonsingularLift ⟦P⟧ := hP ▸ pt.nonsingular
    have hnsP : (W_F).Nonsingular P := hnsL
    have hc : (W_F).Equation P ∧ P ≠ 0 :=
      ⟨hnsP.1, kw_lrApt_ne_zero_of_nonsingular W F hnsP⟩
    have hpteq : pt = ⟨hnsL⟩ := Projective.Point.ext hP.symm
    rw [hpteq]
    refine Projective.Point.ext ?_
    show kw_lrApt_toPointClass W F _ = ⟦P⟧
    rw [kw_lrApt_ofProjPoint_mk W F _ hc.1 hc.2, kw_lrApt_toPointClass_ofVecScheme]

theorem kw_lrApt_projPointEquiv_apply_point (φ : SchemeHomOver (t_F) π) :
    (kw_lrApt_projPointEquiv W F hΔ φ).point = kw_lrApt_toPointClass W F φ :=
  rfl

noncomputable def kw_lrApt_setEquiv :
    SchemeHomOver (t_F) π ≃ (W.baseChange F).toAffine.Point :=
  (kw_lrApt_projPointEquiv W F hΔ).trans
    (Projective.Point.toAffineAddEquiv (W_F)).toEquiv

end Assembly

theorem kwLRAffinePtSetEquiv_kernelNameCheck : True := by
  have _ := kwLRAffinePtSetEquiv_axiomAnchor
  have _ := @kw_lrApt_WF.{0}
  have _ := @kw_lrApt_chartEval.{0}
  have _ := @kw_lrApt_chartEval_self.{0}
  have _ := @kw_lrApt_chartEval_ne_zero.{0}
  have _ := @kw_lrApt_aeval_chartEval.{0}
  have _ := @kw_lrApt_chartEval_equation.{0}
  have _ := @kw_lrApt_toPointClass.{0}
  have _ := @kw_lrApt_nonsingular_of_equation_of_ne_zero.{0}
  have _ := @kw_lrApt_projPointEquiv.{0}
  have _ := @kw_lrApt_setEquiv.{0}
  trivial

end WeierstrassProjModel

set_option autoImplicit false
set_option maxHeartbeats 19200000
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped WeierstrassCurve.Projective

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR projModelCR projModelStrCR IsPointsEval kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrChart_dehom_polynomial kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwYChartEval kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kwYChartEval_gen_eq exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain exists_isCoefficientHom RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel NeronModelInfra"

attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (L : Type u) [Field L] [Algebra R L]

theorem kwLRAffinePtSetEquivGalNat_axiomAnchor : True :=
  have _h₁ : True = True := propext Iff.rfl
  have _h₂ : ℕ := Classical.choice ⟨0⟩
  have _h₃ : Quot.mk (fun (_ _ : ℕ) => True) 0 = Quot.mk (fun (_ _ : ℕ) => True) 1 :=
    Quot.sound trivial
  trivial

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover
set_option quotPrecheck false in
local notation "t_L" => kw_lrAptb_tF (R := R) L
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "W_L" => kw_lrApt_WF W L

theorem kw_lrApt_setEquiv_eq_toAffine_toVec (hΔ : algebraMap R L W.Δ ≠ 0)
    (φ : SchemeHomOver (t_L) π) :
    kw_lrApt_setEquiv W L hΔ φ
      = Projective.Point.toAffine (W_L) (kw_lrApt_toVec W L φ) :=
  rfl

section GalNat

variable {K : Type u} [CommRing K] [Algebra R K] [Algebra K L] [IsScalarTower R K L]

theorem kw_lrApt_hoverσ (σ : L ≃ₐ[K] L) (φ : SchemeHomOver (t_L) π) :
    (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ φ.1) ≫ π = t_L := by
  rw [Category.assoc, φ.2]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (RingHom.ext fun r => (σ.toAlgHom.restrictScalars R).commutes r)

theorem kw_lrApt_precomp_fac (σ : L ≃ₐ[K] L) (φ : SchemeHomOver (t_L) π) :
    (⟨Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ φ.1,
        kw_lrApt_hoverσ W L σ φ⟩ : SchemeHomOver (t_L) π).1
      = Spec.map (CommRingCat.ofHom
            ((σ.toAlgHom.restrictScalars R).comp (kw_lrApt_chartHom W L φ)).toRingHom)
          ≫ (coverE).f (kw_lrApt_chartIdx W L φ) := by
  show Spec.map _ ≫ φ.1 = _
  rw [kw_lrApt_chartHom_fac W L φ, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem kw_lrApt_toPointClass_precomp (σ : L ≃ₐ[K] L) (φ : SchemeHomOver (t_L) π) :
    kw_lrApt_toPointClass W L
        ⟨Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ φ.1, kw_lrApt_hoverσ W L σ φ⟩
      = ⟦σ ∘ (kw_lrApt_toVec W L φ)⟧ := by
  rw [kw_lrApt_toPointClass_eq_of_fac W L _ (kw_lrApt_chartIdx W L φ)
    ((σ.toAlgHom.restrictScalars R).comp (kw_lrApt_chartHom W L φ))
    (kw_lrApt_precomp_fac W L σ φ)]
  rfl

theorem kw_lrApt_WF_map_σ (σ : L ≃ₐ[K] L) :
    (W_L).map σ.toAlgHom.toRingHom = W_L := by
  have h : ∀ r : R, σ.toAlgHom.toRingHom (algebraMap R L r) = algebraMap R L r := fun r => by
    show σ _ = _; rw [IsScalarTower.algebraMap_apply R K L]; exact σ.commutes _
  ext <;> simp only [WeierstrassCurve.map, WeierstrassCurve.baseChange, kw_lrApt_WF] <;>
    exact h _

theorem kw_lrApt_nonsingular_map_σ (σ : L ≃ₐ[K] L) (P : Fin 3 → L) :
    (W_L).Nonsingular (σ ∘ P) ↔ (W_L).Nonsingular P := by
  have h := Projective.map_nonsingular (W_L) (f := σ.toAlgHom.toRingHom)
    (σ.toRingEquiv.injective) P
  rwa [kw_lrApt_WF_map_σ W L σ] at h

theorem kw_lrApt_toAffine_map_comp (σ : L ≃ₐ[K] L) (P : Fin 3 → L)
    (hP : (W_L).Nonsingular P) :
    Projective.Point.toAffine (W_L) (σ ∘ P)
      = (Affine.Point.map (W' := W.toAffine) σ.toAlgHom)
          (Projective.Point.toAffine (W_L) P) := by
  have _ := kwLRAffinePtSetEquivGalNat_axiomAnchor
  have hσinj : Function.Injective (σ : L → L) := σ.injective
  by_cases hz : P 2 = 0
  · rw [Projective.Point.toAffine_of_Z_eq_zero hz,
      Projective.Point.toAffine_of_Z_eq_zero
        (show (σ ∘ P) 2 = 0 by simp only [Function.comp_apply, hz, map_zero]),
      (Affine.Point.map σ.toAlgHom).map_zero]
  · have hz' : (σ ∘ P) 2 ≠ 0 :=
      fun h => hz (hσinj (by simpa using h.trans (map_zero σ).symm))
    have hPσ : (W_L).Nonsingular (σ ∘ P) := (kw_lrApt_nonsingular_map_σ W L σ P).mpr hP
    have hx : (σ ∘ P) 0 / (σ ∘ P) 2 = σ.toAlgHom (P 0 / P 2) := by
      simp only [Function.comp_apply, map_div₀]; rfl
    have hy : (σ ∘ P) 1 / (σ ∘ P) 2 = σ.toAlgHom (P 1 / P 2) := by
      simp only [Function.comp_apply, map_div₀]; rfl
    rw [Projective.Point.toAffine_of_Z_ne_zero hP hz,
      Projective.Point.toAffine_of_Z_ne_zero hPσ hz',
      Affine.Point.map_some]
    simp only [hx, hy]

theorem kw_lrApt_setEquiv_galNat (hΔ : algebraMap R L W.Δ ≠ 0) (σ : L ≃ₐ[K] L)
    (φ : SchemeHomOver (t_L) π) :
    kw_lrApt_setEquiv W L hΔ
        ⟨Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ φ.1, kw_lrApt_hoverσ W L σ φ⟩
      = (Affine.Point.map (W' := W.toAffine) σ.toAlgHom) (kw_lrApt_setEquiv W L hΔ φ) := by
  have _ := kwLRAffinePtSetEquivGalNat_axiomAnchor

  rw [kw_lrApt_setEquiv_eq_toAffine_toVec W L hΔ,
    kw_lrApt_setEquiv_eq_toAffine_toVec W L hΔ]

  have hpt : (kw_lrApt_projPointEquiv W L hΔ
        ⟨_, kw_lrApt_hoverσ W L σ φ⟩).point = ⟦σ ∘ (kw_lrApt_toVec W L φ)⟧ :=
    (kw_lrApt_projPointEquiv_apply_point W L hΔ _).trans
      (kw_lrApt_toPointClass_precomp W L σ φ)
  have hns := (kw_lrApt_projPointEquiv W L hΔ ⟨_, kw_lrApt_hoverσ W L σ φ⟩).nonsingular
  have hPns : (W_L).Nonsingular (kw_lrApt_toVec W L φ) :=
    (kw_lrApt_projPointEquiv W L hΔ φ).nonsingular
  have hσPns : (W_L).NonsingularLift ⟦σ ∘ (kw_lrApt_toVec W L φ)⟧ :=
    (kw_lrApt_nonsingular_map_σ W L σ _).mpr hPns
  have heq : (kw_lrApt_projPointEquiv W L hΔ ⟨_, kw_lrApt_hoverσ W L σ φ⟩)
      = Projective.Point.mk (W' := W_L) (point := ⟦σ ∘ (kw_lrApt_toVec W L φ)⟧) hσPns :=
    Projective.Point.ext hpt
  calc Projective.Point.toAffine (W_L) (kw_lrApt_toVec W L ⟨_, kw_lrApt_hoverσ W L σ φ⟩)
      = (kw_lrApt_projPointEquiv W L hΔ ⟨_, kw_lrApt_hoverσ W L σ φ⟩).toAffineLift := rfl
    _ = (Projective.Point.mk (W' := W_L) (point := ⟦σ ∘ (kw_lrApt_toVec W L φ)⟧)
            hσPns).toAffineLift := by rw [heq]
    _ = Projective.Point.toAffine (W_L) (σ ∘ (kw_lrApt_toVec W L φ)) := rfl
    _ = (Affine.Point.map (W' := W.toAffine) σ.toAlgHom)
          (Projective.Point.toAffine (W_L) (kw_lrApt_toVec W L φ)) :=
        kw_lrApt_toAffine_map_comp W L σ _ hPns

end GalNat

theorem kwLRAffinePtSetEquivGalNat_kernelNameCheck : True := by
  have _ := kwLRAffinePtSetEquivGalNat_axiomAnchor
  have _ := @kw_lrApt_setEquiv_eq_toAffine_toVec.{0}
  have _ := @kw_lrApt_hoverσ.{0}
  have _ := @kw_lrApt_precomp_fac.{0}
  have _ := @kw_lrApt_toPointClass_precomp.{0}
  have _ := @kw_lrApt_WF_map_σ.{0}
  have _ := @kw_lrApt_nonsingular_map_σ.{0}
  have _ := @kw_lrApt_toAffine_map_comp.{0}
  have _ := @kw_lrApt_setEquiv_galNat.{0}
  trivial

end WeierstrassProjModel

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR projModelCR projModelStrCR IsPointsEval kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrChart_dehom_polynomial kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwYChartEval kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kwYChartEval_gen_eq exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain exists_isCoefficientHom RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback"
p2m_open "WeierstrassProjModel"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

section PinBridge

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem kw_pinpe_algebraMap_Δ_ne_zero (hΔ : IsUnit W.Δ)
    (F : Type u) [Field F] [Algebra R F] : algebraMap R F W.Δ ≠ 0 :=
  (hΔ.map (algebraMap R F)).ne_zero

end PinBridge

end WeierstrassProjModel

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR projModelCR projModelStrCR IsPointsEval kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrChart_dehom_polynomial kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwYChartEval kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kwYChartEval_gen_eq exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain exists_isCoefficientHom RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback"
namespace CoordPointsEval
p2m_open "WeierstrassProjModel"

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization MvPolynomial"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (F : Type) [Field F] [Algebra R F]

theorem comp_algebraMap_eq_of_fac
    (P : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (χ : Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →+* F)
    (hfac : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i) :
    χ.comp (algebraMap R _) = algebraMap R F := by
  have h := P.2
  have e2 := kw_lrApt_coverE_f_comp_π W i
  rw [hfac, Category.assoc] at h
  erw [e2, ← Spec.map_comp] at h
  have h2 := Spec.map_injective (h.trans (by rfl : kw_lrAptb_tF (R := R) F = Spec.map (CommRingCat.ofHom (algebraMap R F))))
  have h3 := congrArg CommRingCat.Hom.hom h2
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at h3
  exact h3

def algHomOfFac
    (P : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (χ : Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →+* F)
    (hfac : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i) :
    Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →ₐ[R] F :=
  { toRingHom := χ
    commutes' := fun r ↦ RingHom.congr_fun (comp_algebraMap_eq_of_fac W F P i χ hfac) r }

@[scoped simp] theorem algHomOfFac_toRingHom
    (P : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (χ : Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →+* F)
    (hfac : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i) :
    (algHomOfFac W F P i χ hfac).toRingHom = χ := rfl

theorem toAffine_eq_of_mk_eq {P Q : Fin 3 → F}
    (h : (⟦P⟧ : WeierstrassCurve.Projective.PointClass F) = ⟦Q⟧) :
    WeierstrassCurve.Projective.Point.toAffine (kw_lrApt_WF W F) P =
      WeierstrassCurve.Projective.Point.toAffine (kw_lrApt_WF W F) Q := by
  obtain ⟨u, rfl⟩ := Quotient.eq.mp h
  exact WeierstrassCurve.Projective.Point.toAffine_smul Q u.isUnit

end WeierstrassProjModel.CoordPointsEval
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel.CoordPointsEval"
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR projModelCR projModelStrCR IsPointsEval kw_lrChart_mkX_mem_one kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrChart_dehom_polynomial kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwYChartEval kwZeroSect kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kwYChartEval_gen_eq exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain exists_isCoefficientHom RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback"
namespace PinEvBC
p2m_open "WeierstrassProjModel"

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization MvPolynomial P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel.CoordPointsEval"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

def castOver {R : Type} [CommRing R] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of R)}
    {t₁ t₂ : Y ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x : SchemeHomOver t₁ p) : SchemeHomOver t₂ p :=
  ⟨x.1, x.2.trans h⟩

@[scoped simp] theorem castOver_val {R : Type} [CommRing R] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of R)}
    {t₁ t₂ : Y ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x : SchemeHomOver t₁ p) : (castOver h x).1 = x.1 := rfl

theorem mul_castOver {R : Type} [CommRing R] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R p) {t₁ t₂ : Y ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x y : SchemeHomOver t₁ p) :
    G.mul t₂ (castOver h x) (castOver h y) = castOver h (G.mul t₁ x y) := by
  subst h; rfl

def pointCongr {F : Type} [Field F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point → W₂.toAffine.Point
  | .zero => .zero
  | .some x y hxy => .some x y (h ▸ hxy)

theorem pointCongr_rfl {F : Type} [Field F] {W₁ : WeierstrassCurve F} (P : W₁.toAffine.Point) :
    pointCongr rfl P = P := by
  cases P <;> rfl

theorem pointCongr_add {F : Type} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂)
    (P Q : W₁.toAffine.Point) : pointCongr h (P + Q) = pointCongr h P + pointCongr h Q := by
  subst h; simp only [pointCongr_rfl]

theorem pointCongr_zero {F : Type} [Field F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    pointCongr h (0 : W₁.toAffine.Point) = 0 := rfl

theorem pointCongr_some {F : Type} [Field F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂)
    (x y : F) (hxy : W₁.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hxy) = .some x y (h ▸ hxy) := rfl

section Square

variable {T T' : Type} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
  (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
  (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
    (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
  (hP : IsPullback (Proj.map φ hφ) (projModelStrCR (W.map f)) (projModelStrCR W)
    (Spec.map (CommRingCat.ofHom f)))
  (F : Type) [Field F] [Algebra T' F] [Algebra T F]
  (halg : (algebraMap T' F).comp f = algebraMap T F)

include halg in
theorem specMap_comp_eq :
    Spec.map (CommRingCat.ofHom (algebraMap T' F)) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (algebraMap T F)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, halg]

def push (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f))) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W) :=
  castOver (specMap_comp_eq f F halg)
    ⟨x.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩

@[scoped simp] theorem push_val (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f))) :
    (push W f φ hφ hP F halg x).1 = x.1 ≫ Proj.map φ hφ := rfl

def pull (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W)) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f)) :=
  ⟨hP.lift y.1 (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (by rw [y.2, specMap_comp_eq f F halg]),
    hP.lift_snd _ _ _⟩

theorem push_pull (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W)) :
    push W f φ hφ hP F halg (pull W f φ hφ hP F halg y) = y := by
  apply Subtype.ext
  simp only [push_val, pull, hP.lift_fst]

include halg in
theorem baseChange_map_eq : (W.map f).baseChange F = W.baseChange F := by
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map, halg]

end Square
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel.CoordPointsEval"

section LevelR

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (F : Type) [Field F] [Algebra R F]

def zeroPt : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR W.toProjective) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ (kwZeroSect R W).1,
    by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id]⟩

@[scoped simp] theorem zeroPt_val :
    (zeroPt W F).1 = Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ (kwZeroSect R W).1 := rfl

theorem toPointClass_zeroPt :
    kw_lrApt_toPointClass W F (zeroPt W F) = ⟦![(0 : F), 1, 0]⟧ := by
  have hfac : (zeroPt W F).1 =
      Spec.map (CommRingCat.ofHom ((algebraMap R F).comp (kwYChartEval R W))) ≫
        (projModelAffineOpenCoverCR R W.toProjective).openCover.f (1 : Fin 3) := by
    change Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ (Spec.map (CommRingCat.ofHom (kwYChartEval R W)) ≫ _) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  let ψ := algHomOfFac W F _ 1 _ hfac
  have hcls := kw_lrApt_toPointClass_eq_of_fac W F _ 1 ψ hfac
  have hvec : kw_lrApt_chartEval W F 1 ψ = ![(0 : F), 1, 0] := by
    funext k
    change (algebraMap R F) (kwYChartEval R W (kw_lrChart_gen W 1 k)) = _
    rw [kwYChartEval_gen_eq]
    fin_cases k <;> simp
  rw [hcls, hvec]

theorem setEquiv_zeroPt (hΔF : algebraMap R F W.Δ ≠ 0) :
    kw_lrApt_setEquiv W F hΔF (zeroPt W F) = 0 := by
  rw [kw_lrApt_setEquiv_eq_toAffine_toVec W F hΔF]
  have hcls := toPointClass_zeroPt W F
  change WeierstrassCurve.Projective.Point.toAffine (kw_lrApt_WF W F) (kw_lrApt_toVec W F (zeroPt W F)) = 0
  rw [toAffine_eq_of_mk_eq W F hcls, WeierstrassCurve.Projective.Point.toAffine_zero]

theorem setEquiv_coord (hΔF : algebraMap R F W.Δ ≠ 0)
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR W.toProjective))
    (χ : ZChartRing W.toProjective →+* F)
    (hP : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective) :
    ∃ hxy : (W.toProjective.baseChange F).toAffine.Nonsingular (χ (xOverZ W.toProjective)) (χ (yOverZ W.toProjective)),
      kw_lrApt_setEquiv W F hΔF P = WeierstrassCurve.Affine.Point.some _ _ hxy := by
  have hfac : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3) := by
    rw [hP]; rfl
  let ψ := algHomOfFac W F P 2 χ hfac
  have hcls := kw_lrApt_toPointClass_eq_of_fac W F P 2 ψ hfac
  have hvec : kw_lrApt_chartEval W F 2 ψ = ![χ (xOverZ W.toProjective), χ (yOverZ W.toProjective), 1] := by
    funext k
    fin_cases k
    · change χ (kw_lrChart_gen W 2 0) = χ (xOverZ W.toProjective)
      rw [kw_lrApt_gen_eq_awayMk]; rfl
    · change χ (kw_lrChart_gen W 2 1) = χ (yOverZ W.toProjective)
      rw [kw_lrApt_gen_eq_awayMk]; rfl
    · exact kw_lrApt_chartEval_self W F 2 ψ
  have hns : (kw_lrApt_WF W F).Nonsingular ![χ (xOverZ W.toProjective), χ (yOverZ W.toProjective), 1] := by
    rw [← hvec]
    exact kw_lrApt_nonsingular_of_equation_of_ne_zero W hΔF (kw_lrApt_chartEval_equation W F 2 ψ)
      (kw_lrApt_chartEval_ne_zero W F 2 ψ)
  refine ⟨(WeierstrassCurve.Projective.nonsingular_some _ _).mp hns, ?_⟩
  rw [kw_lrApt_setEquiv_eq_toAffine_toVec W F hΔF,
    toAffine_eq_of_mk_eq W F (hcls.trans (by rw [hvec])), WeierstrassCurve.Projective.Point.toAffine_some]
  exact hns

theorem eq_zeroPt_of_chartEval_two_eq_zero
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR W.toProjective))
    (i : Fin 3)
    (ψ : Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : Q.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    (hz : kw_lrApt_chartEval W F i ψ 2 = 0) :
    Q = zeroPt W F := by
  apply kw_lrApt_toPointClass_injective W F
  rw [kw_lrApt_toPointClass_eq_of_fac W F Q i ψ hfac, toPointClass_zeroPt]
  have heq : (kw_lrApt_WF W F).Equation (kw_lrApt_chartEval W F i ψ) := kw_lrApt_chartEval_equation W F i ψ
  exact ProjWeierstrassDehomog.pointClass_eq_pointAtInfinity (V := kw_lrApt_WF W F) heq hz
    (kw_lrApt_chartEval_ne_zero W F i ψ)

theorem exists_fac_two_of_chartEval_two_ne_zero
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR W.toProjective))
    (i : Fin 3)
    (ψ : Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : Q.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    (hz : kw_lrApt_chartEval W F i ψ 2 ≠ 0) :
    ∃ ψ₂ : Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X 2 : MvPolynomial (Fin 3) R)) →ₐ[R] F,
      Q.1 = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3) := by
  have hz' : ψ (kw_lrChart_gen W i 2) ≠ 0 := hz
  have hrange := kw_lrApt_range_subset_of_gen_ne_zero W F ψ 2 hz'
  refine kw_lrApt_factor_of_range W F Q 2 ?_
  rw [hfac]
  exact hrange

end LevelR
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel.CoordPointsEval"

end WeierstrassProjModel.PinEvBC
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel.CoordPointsEval P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel.PinEvBC"
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel.CoordPointsEval"

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

open WeierstrassProjModel.CoordPointsEval WeierstrassProjModel.PinEvBC MvPolynomial in
set_option maxHeartbeats 6400000 in
theorem solution
    {T : Type} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (G : RelativeGroupLaw T (projModelStrCR W.toProjective))
    (hG : (G.one (𝟙 _)).1 = (kwZeroSect T W).1) :
    ∃ ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W.toProjective) ≃
          (W.toProjective.baseChange F).toAffine.Point,
      IsPointsEval W.toProjective G ev ∧
      (∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
        ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
          by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0) ∧
      ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F]
        (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W.toProjective))
        (χ : ZChartRing W.toProjective →+* F),
        P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective →
        ∃ hxy : (W.toProjective.baseChange F).toAffine.Nonsingular (χ (xOverZ W.toProjective)) (χ (yOverZ W.toProjective)),
          ev F P = WeierstrassCurve.Affine.Point.some _ _ hxy := by
  classical

  have hG' : ∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of T)),
      (G.one s).1 = s ≫ (kwZeroSect T W.toProjective.toAffine).1 := by
    intro S s
    have h := congrArg Subtype.val (G.one_natural (𝟙 _) s s (Category.comp_id s))
    rw [← h]
    show s ≫ (G.one (𝟙 _)).1 = _
    rw [hG]
  refine ⟨fun F _ _ _ ↦ kw_lrApt_setEquiv W F (kw_pinpe_algebraMap_Δ_ne_zero W hΔ F), ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    intro F instF instD instA P Q
    have hΔF := kw_pinpe_algebraMap_Δ_ne_zero W hΔ F

    obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom W.toProjective (algebraMap T F)
    have hP := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom
      W.toProjective (algebraMap T F) φ hφ hcoef

    obtain ⟨GF, hmul, hone⟩ := WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      (algebraMap T F) (projModelStrCR W.toProjective) (projModelStrCR (W.toProjective.map (algebraMap T F)))
      (Proj.map φ hφ) hP G
    have hGF1 : ∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of F)),
        (GF.one s).1 = s ≫ (kwZeroSect F (W.toProjective.map (algebraMap T F)).toAffine).1 :=
      fun s ↦ WeierstrassCurve.DrinfeldGlobal.one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
        W.toProjective (algebraMap T F) φ hφ hcoef hP G GF (fun s ↦ hG' s) (fun s ↦ hone s) s

    haveI : (W.toProjective.map (algebraMap T F)).IsElliptic :=
      ⟨by rw [WeierstrassCurve.map_Δ]; exact hΔ.map _⟩
    obtain ⟨evF, ⟨haddF, -⟩, hzeroF, hcoordF⟩ :=
      WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
        (T := F) (W.toProjective.map (algebraMap T F)) GF (by rw [hGF1 (𝟙 _), Category.id_comp])

    have halg : (algebraMap F F).comp (algebraMap T F) = algebraMap T F := RingHom.ext fun _ ↦ rfl
    have hWF : (W.toProjective.map (algebraMap T F)).baseChange F = W.toProjective.baseChange F :=
      baseChange_map_eq W.toProjective (algebraMap T F) F halg

    have bridge : ∀ Qp : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F F)))
        (projModelStrCR (W.toProjective.map (algebraMap T F))),
        kw_lrApt_setEquiv W F hΔF (push W.toProjective (algebraMap T F) φ hφ hP F halg Qp) =
          pointCongr hWF (evF F Qp) := by
      intro Qp
      obtain ⟨i, ψ, hfac⟩ := kw_lrApt_schemeHom_factor (W.toProjective.map (algebraMap T F)) F Qp
      by_cases hz : kw_lrApt_chartEval (W.toProjective.map (algebraMap T F)) F i ψ 2 = 0
      ·
        have hQ : Qp = zeroPt (W.toProjective.map (algebraMap T F)) F :=
          eq_zeroPt_of_chartEval_two_eq_zero _ F Qp i ψ hfac hz
        rw [hQ]
        have hz0 : evF F (zeroPt (W.toProjective.map (algebraMap T F)) F) = 0 := hzeroF F
        rw [hz0, pointCongr_zero]
        have hpush : push W.toProjective (algebraMap T F) φ hφ hP F halg
            (zeroPt (W.toProjective.map (algebraMap T F)) F) = zeroPt W F := by
          apply Subtype.ext
          rw [push_val, zeroPt_val, zeroPt_val, Category.assoc]
          have h1 := hGF1 (Spec.map (CommRingCat.ofHom (algebraMap F F)))
          have h2 := hone (Spec.map (CommRingCat.ofHom (algebraMap F F)))
          rw [← Category.assoc]
          erw [← h1]
          rw [h2, hG', specMap_comp_eq (algebraMap T F) F halg]
        rw [hpush]
        exact setEquiv_zeroPt W F hΔF
      ·
        obtain ⟨ψ₂, hfac₂⟩ := exists_fac_two_of_chartEval_two_ne_zero _ F Qp i ψ hfac hz
        obtain ⟨hnsF, hevF⟩ := hcoordF F Qp ψ₂.toRingHom (by rw [hfac₂]; rfl)
        obtain ⟨a, ha, hax, hay⟩ :=
          WeierstrassCurve.DrinfeldGlobal.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
            W.toProjective (algebraMap T F) φ hφ hcoef
        have hfacT : (push W.toProjective (algebraMap T F) φ hφ hP F halg Qp).1 =
            Spec.map (CommRingCat.ofHom (ψ₂.toRingHom.comp a)) ≫ zChartι W.toProjective := by
          rw [push_val, hfac₂, Category.assoc]
          change Spec.map (CommRingCat.ofHom ψ₂.toRingHom) ≫
            (zChartι (W.toProjective.map (algebraMap T F)) ≫ Proj.map φ hφ) = _
          rw [ha, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
        obtain ⟨hnsT, hevT⟩ := setEquiv_coord W F hΔF _ (ψ₂.toRingHom.comp a) hfacT
        rw [hevT, hevF, pointCongr_some]
        congr 1
        · rw [RingHom.comp_apply, hax]
        · rw [RingHom.comp_apply, hay]

    have push_mul : ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F F)))
        (projModelStrCR (W.toProjective.map (algebraMap T F))),
        push W.toProjective (algebraMap T F) φ hφ hP F halg
          (GF.mul (Spec.map (CommRingCat.ofHom (algebraMap F F))) x y) =
        G.mul (Spec.map (CommRingCat.ofHom (algebraMap T F)))
          (push W.toProjective (algebraMap T F) φ hφ hP F halg x)
          (push W.toProjective (algebraMap T F) φ hφ hP F halg y) := by
      intro x y
      apply Subtype.ext
      rw [push_val, hmul]
      show _ = (G.mul _ (castOver (specMap_comp_eq (algebraMap T F) F halg) _)
        (castOver (specMap_comp_eq (algebraMap T F) F halg) _)).1
      rw [mul_castOver, castOver_val]

    have hP' := push_pull W.toProjective (algebraMap T F) φ hφ hP F halg P
    have hQ' := push_pull W.toProjective (algebraMap T F) φ hφ hP F halg Q
    show kw_lrApt_setEquiv W F hΔF (G.mul _ P Q) = kw_lrApt_setEquiv W F hΔF P + kw_lrApt_setEquiv W F hΔF Q
    rw [← hP', ← hQ', ← push_mul, bridge, bridge, bridge, haddF, pointCongr_add]
  ·
    intro F instF instD instA σ P
    have hdec : instD = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
    subst hdec
    exact kw_lrApt_setEquiv_galNat W F (kw_pinpe_algebraMap_Δ_ne_zero W hΔ F) (K := T) σ P
  ·
    intro F instF instD instA
    exact setEquiv_zeroPt W F (kw_pinpe_algebraMap_Δ_ne_zero W hΔ F)
  ·
    intro F instF instD instA P χ hP
    exact setEquiv_coord W F (kw_pinpe_algebraMap_Δ_ne_zero W hΔ F) P χ hP

end
end
end S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion
end P2MW
export P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion (solution)

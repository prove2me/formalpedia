-- Prove2me | solution 1 for WeierstrassProjModel.kw_a2_sixU_class_eq_addMap_of_delta_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9b892384-27ee-599f-b86d-73d72b55ab48

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_a2_checks_addXYZ_crossXZ
import Theorems.Thm_WeierstrassProjModel_kw_a2_checks_crossYZ
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero

set_option autoImplicit false
set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped WeierstrassCurve.Projective

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR projModelCR projModelStrCR kw_lrAdd_WP₁ kw_lrAdd_WP₂ kw_lrAdd_X kw_lrAdd_Y kw_lrAdd_Z kw_lrSym_X kw_lrSym_Y kw_lrSym_Z kw_lrSym_minor_XZ kw_lrSym_minor_YZ kw_lrAdd_vec kw_lrComul_biIdeal kw_lrComul_biGrading kw_lrAdd_comulHom kw_lrAdd_comulHom_mk_X kw_lrSym_vec kw_lrSym_comulHom kw_lrSym_comulHom_mk_X kw_lrChart_mkX_mem_one kw_lrChart_aux kw_lrChart_aux_mk kw_lrChart_aux_range_subset kw_lrChart_away kw_pbac_awayAlgebra kw_lrChart_gen kw_lrChart_gen_val kw_lrChart_dehom kw_lrChart_mk_mem_of_isHomogeneous kw_lrChart_dehom_isHomogeneous kw_lrChart_dehom_polynomial kw_lrChart_inL kw_lrChart_inR kw_lrChart_ev kw_lrChart_ev' kw_lrChart_u kw_lrChart_toTensorLoc kw_lrChart_tensor kw_lrSymChart_aux kw_lrSymChart_aux_mk kw_lrSymChart_aux_range_subset kw_lrSymChart_away kw_lrSymChart_u kw_lrSymChart_toTensorLoc kw_lrSymChart_tensor kw_lrSixU kw_lrSixU_cover kw_lrSixU_toE kw_lrSixU_locMap kw_pbac_mk_X_mem_one_CR projModelAffineOpenCoverCR kw_pbac_awayι_comp_projModelStrCR kwProjPullbackChartIsoCR kw_lrAptb_tF kw_lrApt_WF kw_lrApt_chartEval kw_a2_checks_addXYZ_crossXZ kw_a2_checks_crossYZ"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero.WeierstrassProjModel NeronModelInfra"

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

end Inverse

abbrev kw_lrBihom_wL : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

local notation "wL" => @kw_lrBihom_wL

theorem kw_lrBihom_isWeightedHomogeneous_Xl_wL (k : Fin 3) :
    (X (Sum.inl k) : MvPolynomial (Fin 3 ⊕ Fin 3) R).IsWeightedHomogeneous kw_lrBihom_wL 1 :=
  isWeightedHomogeneous_X R kw_lrBihom_wL _

theorem kw_lrBihom_isWeightedHomogeneous_Xr_wL (k : Fin 3) :
    (X (Sum.inr k) : MvPolynomial (Fin 3 ⊕ Fin 3) R).IsWeightedHomogeneous kw_lrBihom_wL 0 :=
  isWeightedHomogeneous_X R kw_lrBihom_wL _

theorem kw_lrBihom_isWeightedHomogeneous_Xl_wL_pow (k : Fin 3) (n : ℕ) :
    (X (Sum.inl k) ^ n : MvPolynomial (Fin 3 ⊕ Fin 3) R).IsWeightedHomogeneous kw_lrBihom_wL n := by
  simpa using (kw_lrBihom_isWeightedHomogeneous_Xl_wL (R := R) k).pow n

theorem kw_lrBihom_isWeightedHomogeneous_Xr_wL_pow (k : Fin 3) (n : ℕ) :
    (X (Sum.inr k) ^ n : MvPolynomial (Fin 3 ⊕ Fin 3) R).IsWeightedHomogeneous kw_lrBihom_wL 0 := by
  simpa using (kw_lrBihom_isWeightedHomogeneous_Xr_wL (R := R) k).pow n

local macro "peel_bihom_L" : tactic =>
  `(tactic| repeat' first
    | with_reducible apply IsWeightedHomogeneous.add
    | with_reducible exact isWeightedHomogeneous_C _ _
    | with_reducible refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_isWeightedHomogeneous_Xl_wL _)
    | with_reducible refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_isWeightedHomogeneous_Xr_wL _)
    | with_reducible refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_isWeightedHomogeneous_Xl_wL_pow _ _)
    | with_reducible refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_isWeightedHomogeneous_Xr_wL_pow _ _))

theorem kw_lrSymBihom_lrSymX_wL : (kw_lrSym_X W).IsWeightedHomogeneous wL 2 := by
  unfold kw_lrSym_X; peel_bihom_L

theorem kw_lrSymBihom_lrSymY_wL : (kw_lrSym_Y W).IsWeightedHomogeneous wL 2 := by
  unfold kw_lrSym_Y; peel_bihom_L

theorem kw_lrSymBihom_lrSymZ_wL : (kw_lrSym_Z W).IsWeightedHomogeneous wL 2 := by
  unfold kw_lrSym_Z; peel_bihom_L

section SixUInline

open scoped TensorProduct

variable (i j k : Fin 3)

set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal
local notation "ℬ" => ProjModelRingCR W.toProjective

theorem kw_lrChart_away_val (k : Fin 3) (z : 𝒜 k) :
    (kw_lrChart_away W k z).val = kw_lrChart_aux W k z := by
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (HomogeneousLocalization.Away (kw_lrComul_biGrading W)
        (mk₆ (kw_lrAdd_vec W k))) (Localization.Away (mk₆ (kw_lrAdd_vec W k))))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  show (e (e.symm ⟨kw_lrChart_aux W k z,
      kw_lrChart_aux_range_subset W k ⟨z, rfl⟩⟩)).1 = kw_lrChart_aux W k z
  rw [e.apply_symm_apply]

theorem kw_lrSymChart_away_val (k : Fin 3) (z : 𝒜 k) :
    (kw_lrSymChart_away W k z).val = kw_lrSymChart_aux W k z := by
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (HomogeneousLocalization.Away (kw_lrComul_biGrading W)
        (mk₆ (kw_lrSym_vec W k))) (Localization.Away (mk₆ (kw_lrSym_vec W k))))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  show (e (e.symm ⟨kw_lrSymChart_aux W k z,
      kw_lrSymChart_aux_range_subset W k ⟨z, rfl⟩⟩)).1 = kw_lrSymChart_aux W k z
  rw [e.apply_symm_apply]

theorem kw_lrChart_ev'_mk (i j : Fin 3) (a : MvPolynomial (Fin 3 ⊕ Fin 3) R) :
    kw_lrChart_ev' W i j (mk₆ a) = kw_lrChart_ev W i j a := by
  rfl

theorem kw_lrChart_tensor_mk (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    kw_lrChart_tensor W i j k
        (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W k) n a ha)
      = Localization.mk (kw_lrChart_ev' W i j (kw_lrAdd_comulHom W a))
          (⟨kw_lrChart_u W i j k ^ n, n, rfl⟩
            : Submonoid.powers (kw_lrChart_u W i j k)) := by
  show kw_lrChart_toTensorLoc W i j k
      (kw_lrChart_away W k
        (HomogeneousLocalization.Away.mk _ (kw_lrChart_mkX_mem_one W k) n a ha)).val = _
  rw [kw_lrChart_away_val, kw_lrChart_aux_mk, Localization.mk_eq_mk',
    kw_lrChart_toTensorLoc, IsLocalization.map_mk', ← Localization.mk_eq_mk']

  congr 1
  refine Subtype.ext ?_
  simp only [map_pow]
  rfl

theorem kw_lrSymChart_tensor_mk (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    kw_lrSymChart_tensor W i j k
        (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W k) n a ha)
      = Localization.mk (kw_lrChart_ev' W i j (kw_lrSym_comulHom W a))
          (⟨kw_lrSymChart_u W i j k ^ n, n, rfl⟩
            : Submonoid.powers (kw_lrSymChart_u W i j k)) := by
  show kw_lrSymChart_toTensorLoc W i j k
      (kw_lrSymChart_away W k
        (HomogeneousLocalization.Away.mk _ (kw_lrChart_mkX_mem_one W k) n a ha)).val = _
  rw [kw_lrSymChart_away_val, kw_lrSymChart_aux_mk, Localization.mk_eq_mk',
    kw_lrSymChart_toTensorLoc, IsLocalization.map_mk', ← Localization.mk_eq_mk']

  congr 1
  refine Subtype.ext ?_
  simp only [map_pow]
  rfl

theorem kw_lrChart_tensor_comp_algebraMap :
    (kw_lrChart_tensor W i j k).comp (algebraMap R (𝒜 k))
      = (algebraMap ((𝒜 i) ⊗[R] (𝒜 j))
            (Localization.Away (kw_lrChart_u W i j k))).comp
          (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j))) := by
  ext r
  have h1 : algebraMap R (𝒜 k) r
      = HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W k) 0 (mk₃ (C r : MvPolynomial (Fin 3) R))
          (kw_lrChart_mk_mem_of_isHomogeneous W 0 (C r) (isHomogeneous_C _ r)) := by
    have := kw_lrChart_dehom_isHomogeneous W k 0 (C r) (isHomogeneous_C _ r)
    rwa [kw_lrChart_dehom, aeval_C] at this
  rw [RingHom.comp_apply, h1, kw_lrChart_tensor_mk]
  have h2 : kw_lrChart_ev' W i j
        (kw_lrAdd_comulHom W (mk₃ (C r : MvPolynomial (Fin 3) R)))
      = algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)) r := by
    have h := ((kw_lrChart_ev' W i j).comp (kw_lrAdd_comulHom W)).commutes r
    first
      | simpa only [AlgHom.comp_apply] using h
      | (simp only [AlgHom.comp_apply] at h; exact h)
  have hden : (⟨kw_lrChart_u W i j k ^ 0, 0, rfl⟩
      : Submonoid.powers (kw_lrChart_u W i j k)) = 1 := Subtype.ext (pow_zero _)
  rw [h2, hden, Localization.mk_one_eq_algebraMap, RingHom.comp_apply]

theorem kw_lrSymChart_tensor_comp_algebraMap :
    (kw_lrSymChart_tensor W i j k).comp (algebraMap R (𝒜 k))
      = (algebraMap ((𝒜 i) ⊗[R] (𝒜 j))
            (Localization.Away (kw_lrSymChart_u W i j k))).comp
          (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j))) := by
  ext r
  have h1 : algebraMap R (𝒜 k) r
      = HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W k) 0 (mk₃ (C r : MvPolynomial (Fin 3) R))
          (kw_lrChart_mk_mem_of_isHomogeneous W 0 (C r) (isHomogeneous_C _ r)) := by
    have := kw_lrChart_dehom_isHomogeneous W k 0 (C r) (isHomogeneous_C _ r)
    rwa [kw_lrChart_dehom, aeval_C] at this
  rw [RingHom.comp_apply, h1, kw_lrSymChart_tensor_mk]
  have h2 : kw_lrChart_ev' W i j
        (kw_lrSym_comulHom W (mk₃ (C r : MvPolynomial (Fin 3) R)))
      = algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)) r := by
    have h := ((kw_lrChart_ev' W i j).comp (kw_lrSym_comulHom W)).commutes r
    first
      | simpa only [AlgHom.comp_apply] using h
      | (simp only [AlgHom.comp_apply] at h; exact h)
  have hden : (⟨kw_lrSymChart_u W i j k ^ 0, 0, rfl⟩
      : Submonoid.powers (kw_lrSymChart_u W i j k)) = 1 := Subtype.ext (pow_zero _)
  rw [h2, hden, Localization.mk_one_eq_algebraMap, RingHom.comp_apply]

theorem kw_lrSixU_cover_openCover_f
    (h : Ideal.span (Set.range (kw_lrSixU W i j)) = ⊤) (l : Fin 3 ⊕ Fin 3) :
    (kw_lrSixU_cover W i j h).openCover.f l = kw_lrSixU_locMap W i j l := rfl

theorem kw_lrAddMorphismOver_coverL_f_comp :
    (projModelAffineOpenCoverCR R W.toProjective).openCover.f i
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) :=
  kw_pbac_awayι_comp_projModelStrCR R W.toProjective i

theorem kw_lrAddMorphismOver_chartIso_hom_base :
    (kwProjPullbackChartIsoCR R W.toProjective i j).hom
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j))))
      = pullback.fst ((projModelAffineOpenCoverCR R W.toProjective).openCover.f i
            ≫ projModelStrCR W.toProjective)
          ((projModelAffineOpenCoverCR R W.toProjective).openCover.f j
            ≫ projModelStrCR W.toProjective)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) := by
  refine .trans (Category.assoc
      (pullback.congrHom (kw_pbac_awayι_comp_projModelStrCR R W.toProjective i)
        (kw_pbac_awayι_comp_projModelStrCR R W.toProjective j)).hom
      (pullbackSpecIso R (𝒜 i) (𝒜 j)).hom _) ?_
  rw [pullbackSpecIso_hom_base, pullback.congrHom_hom,
    pullback.lift_fst_assoc, Category.comp_id]
  rfl

theorem kw_lrSixU_inl (i j k : Fin 3) :
    kw_lrSixU W i j (Sum.inl k) = kw_lrChart_u W i j k := by
  rfl

theorem kw_lrSixU_inr (i j k : Fin 3) :
    kw_lrSixU W i j (Sum.inr k) = kw_lrSymChart_u W i j k := by
  rfl

theorem kw_lrAddMorphismOver_awayι_comp :
    Proj.awayι (projModelGradingCR W.toProjective) _ (kw_lrChart_mkX_mem_one W k) one_pos
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 k))) :=
  kw_pbac_awayι_comp_projModelStrCR R W.toProjective k

theorem kw_lrSixU_toE_inl (k : Fin 3) :
    kw_lrSixU_toE W i j (Sum.inl k)
      = Spec.map (CommRingCat.ofHom (kw_lrChart_tensor W i j k))
          ≫ Proj.awayι (projModelGradingCR W.toProjective) _
              (kw_lrChart_mkX_mem_one W k) one_pos := rfl

theorem kw_lrSixU_toE_inr (k : Fin 3) :
    kw_lrSixU_toE W i j (Sum.inr k)
      = Spec.map (CommRingCat.ofHom (kw_lrSymChart_tensor W i j k))
          ≫ Proj.awayι (projModelGradingCR W.toProjective) _
              (kw_lrChart_mkX_mem_one W k) one_pos := rfl

theorem kw_lrSixU_toE_over (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    kw_lrSixU_toE W i j l ≫ projModelStrCR W.toProjective
      = kw_lrSixU_locMap W i j l
          ≫ Spec.map (CommRingCat.ofHom (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)))) := by

  obtain ⟨k⟩ | ⟨k⟩ := l <;>
    simp only [kw_lrSixU_toE, kw_lrSixU_locMap, Category.assoc,
      kw_lrAddMorphismOver_awayι_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · exact congrArg (Spec.map <| CommRingCat.ofHom ·)
      (kw_lrChart_tensor_comp_algebraMap W i j k)
  · exact congrArg (Spec.map <| CommRingCat.ofHom ·)
      (kw_lrSymChart_tensor_comp_algebraMap W i j k)

end SixUInline

section Coeff

theorem kw_lrApt_WF_a₁ : (W_F).a₁ = algebraMap R F W.a₁ := rfl
theorem kw_lrApt_WF_a₂ : (W_F).a₂ = algebraMap R F W.a₂ := rfl
theorem kw_lrApt_WF_a₃ : (W_F).a₃ = algebraMap R F W.a₃ := rfl
theorem kw_lrApt_WF_a₄ : (W_F).a₄ = algebraMap R F W.a₄ := rfl
theorem kw_lrApt_WF_a₆ : (W_F).a₆ = algebraMap R F W.a₆ := rfl

end Coeff

section Check1

theorem kw_lrApt_aeval_lrAdd_X (P Q : Fin 3 → F) :
    aeval (Sum.elim P Q) (kw_lrAdd_X W) = -(W_F).addX P Q :=
  (kw_a2_checks_addXYZ_crossXZ W F).1 P Q

theorem kw_lrApt_aeval_lrAdd_Y (P Q : Fin 3 → F) :
    aeval (Sum.elim P Q) (kw_lrAdd_Y W) = -(W_F).addY P Q :=
  (kw_a2_checks_addXYZ_crossXZ W F).2.1 P Q

theorem kw_lrApt_aeval_lrAdd_Z (P Q : Fin 3 → F) :
    aeval (Sum.elim P Q) (kw_lrAdd_Z W) = -(W_F).addZ P Q :=
  (kw_a2_checks_addXYZ_crossXZ W F).2.2.1 P Q

end Check1

section Check2b

theorem kw_lrApt_aeval_lrSym_cross_XZ {P : Fin 3 → F} (hP : (W_F).Equation P) :
    aeval (Sum.elim P P) (kw_lrSym_X W) * (W_F).dblZ P
      = aeval (Sum.elim P P) (kw_lrSym_Z W) * (W_F).dblX P :=
  (kw_a2_checks_addXYZ_crossXZ W F).2.2.2 P hP

theorem kw_lrApt_aeval_lrSym_cross_YZ {P : Fin 3 → F} (hP : (W_F).Equation P) :
    aeval (Sum.elim P P) (kw_lrSym_Y W) * (W_F).dblZ P
      = aeval (Sum.elim P P) (kw_lrSym_Z W) * (W_F).dblY P :=
  kw_a2_checks_crossYZ W F P hP

end Check2b

section MapMulRaw

open scoped TensorProduct WeierstrassCurve.Projective

variable (hΔ : algebraMap R F W.Δ ≠ 0)

section P2Helpers

variable (i j : Fin 3)

theorem kw_lrApt_chartIso_inv_fst :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ pullback.fst _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j))) := by
  simp only [kwProjPullbackChartIsoCR, Iso.trans_inv, Category.assoc]
  rw [pullback.congrHom_inv]
  erw [pullback.lift_fst]
  rw [Category.comp_id]
  exact pullbackSpecIso_inv_fst R (𝒜 i) (𝒜 j)

theorem kw_lrApt_chartIso_inv_snd :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ pullback.snd _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)).toRingHom) := by
  simp only [kwProjPullbackChartIsoCR, Iso.trans_inv, Category.assoc]
  rw [pullback.congrHom_inv]
  erw [pullback.lift_snd]
  rw [Category.comp_id]
  exact pullbackSpecIso_inv_snd R (𝒜 i) (𝒜 j)

end P2Helpers

theorem kw_lrApt_psiTens_comp_ev (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) :
    (Algebra.TensorProduct.productMap ψᵢ ψⱼ).comp (kw_lrChart_ev W i j)
      = aeval (Sum.elim (kw_lrApt_chartEval W F i ψᵢ) (kw_lrApt_chartEval W F j ψⱼ)) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with m | m
  · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inl, kw_lrChart_inL,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, mul_one, kw_lrApt_chartEval]
  · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inr, kw_lrChart_inR,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, one_mul, kw_lrApt_chartEval]

theorem kw_lrApt_psiTens_sixU (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) (l : Fin 3 ⊕ Fin 3) :
    (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l)
      = aeval (Sum.elim (kw_lrApt_chartEval W F i ψᵢ) (kw_lrApt_chartEval W F j ψⱼ))
          (Sum.elim (kw_lrAdd_vec W) (kw_lrSym_vec W) l) := by
  have hd := kw_lrApt_psiTens_comp_ev W F i j ψᵢ ψⱼ
  rcases l with k | k
  · rw [kw_lrSixU_inl, kw_lrChart_u, kw_lrChart_ev'_mk, Sum.elim_inl,
      ← hd, AlgHom.comp_apply]
  · rw [kw_lrSixU_inr, kw_lrSymChart_u, kw_lrChart_ev'_mk, Sum.elim_inr,
      ← hd, AlgHom.comp_apply]

theorem kw_lrApt_aeval_lrAdd_vec (P Q : Fin 3 → F) (k : Fin 3) :
    aeval (Sum.elim P Q) (kw_lrAdd_vec W k) = -(W_F).addXYZ P Q k := by
  fin_cases k
  · exact kw_lrApt_aeval_lrAdd_X W F P Q
  · exact kw_lrApt_aeval_lrAdd_Y W F P Q
  · exact kw_lrApt_aeval_lrAdd_Z W F P Q

section P2Factor

theorem kw_lrApt_chartEval_inl (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) (k : Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j (Sum.inl k)))) :
    ∃ ψres : (𝒜 k) →ₐ[R] F,
      (Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j (Sum.inl k))
            (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
        ≫ kw_lrSixU_toE W i j (Sum.inl k)
      = Spec.map (CommRingCat.ofHom ψres.toRingHom) ≫ (coverE).f k)
      ∧ ∀ m, kw_lrApt_chartEval W F k ψres m
          = -(W_F).addXYZ (kw_lrApt_chartEval W F i ψᵢ) (kw_lrApt_chartEval W F j ψⱼ) m
              / -(W_F).addXYZ (kw_lrApt_chartEval W F i ψᵢ) (kw_lrApt_chartEval W F j ψⱼ) k := by
  set P := kw_lrApt_chartEval W F i ψᵢ
  set Q := kw_lrApt_chartEval W F j ψⱼ

  set L := IsLocalization.Away.lift (S := Localization.Away (kw_lrSixU W i j (Sum.inl k)))
    (kw_lrSixU W i j (Sum.inl k))
    (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu with hLdef

  let ψres_rh : (𝒜 k) →+* F := L.comp (kw_lrChart_tensor W i j k)

  have hLc : ∀ a, L (algebraMap ((𝒜 i) ⊗[R] (𝒜 j))
        (Localization.Away (kw_lrSixU W i j (Sum.inl k))) a)
      = (Algebra.TensorProduct.productMap ψᵢ ψⱼ) a := fun a => by
    rw [hLdef, IsLocalization.Away.lift, IsLocalization.lift_eq]; rfl

  have hψev : ∀ p, (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom
      (kw_lrChart_ev W i j p) = aeval (Sum.elim P Q) p := fun p =>
    DFunLike.congr_fun (kw_lrApt_psiTens_comp_ev W F i j ψᵢ ψⱼ) p

  have hcomm : ψres_rh.comp (algebraMap R (𝒜 k)) = algebraMap R F := by
    ext r
    show L (kw_lrChart_tensor W i j k (algebraMap R (𝒜 k) r)) = algebraMap R F r
    have h1 := RingHom.congr_fun (kw_lrChart_tensor_comp_algebraMap W i j k) r
    simp only [RingHom.comp_apply] at h1
    erw [h1, hLc]
    exact (Algebra.TensorProduct.productMap ψᵢ ψⱼ).commutes r
  let ψres : (𝒜 k) →ₐ[R] F := ⟨ψres_rh, RingHom.congr_fun hcomm⟩
  refine ⟨ψres, ?_, ?_⟩
  ·

    rw [kw_lrSixU_toE_inl]
    refine (Category.assoc _ _ _).symm.trans ?_
    erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  ·
    intro m
    show L (kw_lrChart_tensor W i j k (gen k m)) = _

    rw [kw_lrApt_gen_eq_awayMk W k m]
    erw [kw_lrChart_tensor_mk W i j k 1
      (mk₃ (X m : MvPolynomial (Fin 3) R))
      (kw_lrChart_mk_mem_of_isHomogeneous W 1 (X m) (isHomogeneous_X R m))]

    rw [kw_lrAdd_comulHom_mk_X, kw_lrChart_ev'_mk]

    rw [hLdef, Localization.mk_eq_mk', IsLocalization.Away.lift]
    erw [IsLocalization.lift_mk']
    rw [Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.restrict_apply, MonoidHom.coe_coe,
      pow_one]

    rw [hψev, show kw_lrChart_u W i j k = kw_lrChart_ev W i j (kw_lrAdd_vec W k) from
        (kw_lrChart_ev'_mk W i j _).symm ▸ rfl,
      hψev, kw_lrApt_aeval_lrAdd_vec W F P Q m, kw_lrApt_aeval_lrAdd_vec W F P Q k]

    have hk : (W_F).addXYZ P Q k ≠ 0 := by
      have hthis := kw_lrApt_psiTens_sixU W F i j ψᵢ ψⱼ (Sum.inl k)
      rw [Sum.elim_inl, kw_lrApt_aeval_lrAdd_vec W F P Q k] at hthis
      exact neg_ne_zero.mp (isUnit_iff_ne_zero.mp (hthis ▸ hu))
    rw [neg_div_neg_eq, mul_neg, div_mul_cancel₀ _ hk]

theorem kw_lrApt_chartEval_inr (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) (k : Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j (Sum.inr k)))) :
    ∃ ψres : (𝒜 k) →ₐ[R] F,
      (Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j (Sum.inr k))
            (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
        ≫ kw_lrSixU_toE W i j (Sum.inr k)
      = Spec.map (CommRingCat.ofHom ψres.toRingHom) ≫ (coverE).f k)
      ∧ ∀ m, kw_lrApt_chartEval W F k ψres m
          = aeval (Sum.elim (kw_lrApt_chartEval W F i ψᵢ) (kw_lrApt_chartEval W F j ψⱼ))
                (kw_lrSym_vec W m)
              / aeval (Sum.elim (kw_lrApt_chartEval W F i ψᵢ) (kw_lrApt_chartEval W F j ψⱼ))
                (kw_lrSym_vec W k) := by
  set P := kw_lrApt_chartEval W F i ψᵢ
  set Q := kw_lrApt_chartEval W F j ψⱼ

  set L := IsLocalization.Away.lift (S := Localization.Away (kw_lrSixU W i j (Sum.inr k)))
    (kw_lrSixU W i j (Sum.inr k))
    (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu with hLdef
  let ψres_rh : (𝒜 k) →+* F := L.comp (kw_lrSymChart_tensor W i j k)
  have hLc : ∀ a, L (algebraMap ((𝒜 i) ⊗[R] (𝒜 j))
        (Localization.Away (kw_lrSixU W i j (Sum.inr k))) a)
      = (Algebra.TensorProduct.productMap ψᵢ ψⱼ) a := fun a => by
    rw [hLdef, IsLocalization.Away.lift, IsLocalization.lift_eq]; rfl
  have hψev : ∀ p, (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom
      (kw_lrChart_ev W i j p) = aeval (Sum.elim P Q) p := fun p =>
    DFunLike.congr_fun (kw_lrApt_psiTens_comp_ev W F i j ψᵢ ψⱼ) p

  have hcomm : ψres_rh.comp (algebraMap R (𝒜 k)) = algebraMap R F := by
    ext r
    show L (kw_lrSymChart_tensor W i j k (algebraMap R (𝒜 k) r)) = algebraMap R F r
    have h1 := RingHom.congr_fun (kw_lrSymChart_tensor_comp_algebraMap W i j k) r
    simp only [RingHom.comp_apply] at h1
    erw [h1, hLc]
    exact (Algebra.TensorProduct.productMap ψᵢ ψⱼ).commutes r
  let ψres : (𝒜 k) →ₐ[R] F := ⟨ψres_rh, RingHom.congr_fun hcomm⟩
  refine ⟨ψres, ?_, ?_⟩
  ·
    rw [kw_lrSixU_toE_inr]
    refine (Category.assoc _ _ _).symm.trans ?_
    erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  ·
    intro m
    show L (kw_lrSymChart_tensor W i j k (gen k m)) = _
    rw [kw_lrApt_gen_eq_awayMk W k m]
    erw [kw_lrSymChart_tensor_mk W i j k 1
      (mk₃ (X m : MvPolynomial (Fin 3) R))
      (kw_lrChart_mk_mem_of_isHomogeneous W 1 (X m) (isHomogeneous_X R m))]
    rw [kw_lrSym_comulHom_mk_X, kw_lrChart_ev'_mk]
    rw [hLdef, Localization.mk_eq_mk', IsLocalization.Away.lift]
    erw [IsLocalization.lift_mk']
    rw [Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.restrict_apply, MonoidHom.coe_coe,
      pow_one]

    rw [hψev, show kw_lrSymChart_u W i j k = kw_lrChart_ev W i j (kw_lrSym_vec W k) from
        (kw_lrChart_ev'_mk W i j _).symm ▸ rfl,
      hψev]
    have hk : aeval (Sum.elim P Q) (kw_lrSym_vec W k) ≠ 0 := by
      have hthis := kw_lrApt_psiTens_sixU W F i j ψᵢ ψⱼ (Sum.inr k)
      rw [Sum.elim_inr] at hthis
      exact isUnit_iff_ne_zero.mp (hthis ▸ hu)
    field_simp

end P2Factor

theorem kw_lrApt_prop_of_cross_zero {v w : Fin 3 → F}
    (hXZ : v 0 * w 2 = v 2 * w 0) (hYZ : v 1 * w 2 = v 2 * w 1)
    (hvE : (W_F).Equation v) (hwE : (W_F).Equation w)
    (hvnz : v ≠ 0) (hwnz : w ≠ 0) :
    (⟦v⟧ : Projective.PointClass F) = ⟦w⟧ := by
  by_cases hv2 : v 2 = 0
  ·

    have hv0 : v 0 = 0 := Projective.X_eq_zero_of_Z_eq_zero hvE hv2
    have hv1 : v 1 ≠ 0 := fun h => hvnz (funext fun m => by
      fin_cases m
      exacts [hv0, h, hv2])
    have hw2 : w 2 = 0 := by
      have h := hYZ; rw [hv2, zero_mul] at h
      exact (mul_eq_zero.mp h).resolve_left hv1
    have hw0 : w 0 = 0 := Projective.X_eq_zero_of_Z_eq_zero hwE hw2
    have hw1 : w 1 ≠ 0 := fun h => hwnz (funext fun m => by
      fin_cases m
      exacts [hw0, h, hw2])
    rw [show v = (v 1 / w 1) • w from funext fun m => by
      rw [Pi.smul_apply, smul_eq_mul]
      fin_cases m
      · show v 0 = v 1 / w 1 * w 0; rw [hv0, hw0, mul_zero]
      · show v 1 = v 1 / w 1 * w 1; rw [div_mul_cancel₀ _ hw1]
      · show v 2 = v 1 / w 1 * w 2; rw [hv2, hw2, mul_zero]]
    exact Projective.smul_eq _ (isUnit_iff_ne_zero.mpr (div_ne_zero hv1 hw1))
  · by_cases hw2 : w 2 = 0
    ·
      have hw0 : w 0 = 0 := by
        have h := hXZ; rw [hw2, mul_zero] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hv2
      have hw1 : w 1 = 0 := by
        have h := hYZ; rw [hw2, mul_zero] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hv2
      exact absurd (_root_.funext fun m => by
        fin_cases m
        exacts [hw0, hw1, hw2]) hwnz
    ·
      rw [show v = (v 2 / w 2) • w from funext fun m => by
        rw [Pi.smul_apply, smul_eq_mul]
        fin_cases m
        · show v 0 = v 2 / w 2 * w 0
          rw [div_mul_eq_mul_div, ← hXZ, mul_div_assoc, div_self hw2, mul_one]
        · show v 1 = v 2 / w 2 * w 1
          rw [div_mul_eq_mul_div, ← hYZ, mul_div_assoc, div_self hw2, mul_one]
        · show v 2 = v 2 / w 2 * w 2; rw [div_mul_cancel₀ _ hw2]]
      exact Projective.smul_eq _ (isUnit_iff_ne_zero.mpr (div_ne_zero hv2 hw2))

omit W in

theorem kw_lrApt_aeval_weighted_scaling {σ S : Type*} [CommSemiring S] [Algebra R S]
    (w : σ → ℕ) {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsWeightedHomogeneous w n)
    (t : S) (x : σ → S) :
    aeval (fun i => t ^ w i * x i) φ = t ^ n * aeval x φ := by
  classical
  rw [aeval_def, aeval_def]
  simp only [eval₂_eq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hsum : ∑ i ∈ d.support, d i * w i = n := by
    have h := hφ (mem_support_iff.mp hd)
    rw [Finsupp.weight_apply] at h
    simpa [Finsupp.sum, smul_eq_mul, nsmul_eq_mul] using h
  have hprod : (∏ i ∈ d.support, (t ^ w i * x i) ^ d i)
      = t ^ n * ∏ i ∈ d.support, x i ^ d i := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_pow, ← pow_mul, Nat.mul_comm (w i) (d i)]
  rw [hprod]; exact mul_left_comm _ _ _

theorem kw_lrApt_aeval_WP₁ {P Q : Fin 3 → F} (hP : (W_F).Equation P) :
    aeval (Sum.elim P Q) (kw_lrAdd_WP₁ W) = 0 := by
  rw [kw_lrAdd_WP₁, aeval_rename,
    show Sum.elim P Q ∘ Sum.inl = P from funext fun _ => rfl,
    aeval_def, ← MvPolynomial.eval_map, ← Projective.map_polynomial]
  exact hP

theorem kw_lrApt_aeval_WP₂ {P Q : Fin 3 → F} (hQ : (W_F).Equation Q) :
    aeval (Sum.elim P Q) (kw_lrAdd_WP₂ W) = 0 := by
  rw [kw_lrAdd_WP₂, aeval_rename,
    show Sum.elim P Q ∘ Sum.inr = Q from funext fun _ => rfl,
    aeval_def, ← MvPolynomial.eval_map, ← Projective.map_polynomial]
  exact hQ

theorem kw_lrApt_aeval_minor_XZ {P Q : Fin 3 → F}
    (hP : (W_F).Equation P) (hQ : (W_F).Equation Q) :
    aeval (Sum.elim P Q) (kw_lrSym_vec W 0) * (W_F).addXYZ P Q 2
      = aeval (Sum.elim P Q) (kw_lrSym_vec W 2) * (W_F).addXYZ P Q 0 := by
  have hminor := congrArg (aeval (R := R) (Sum.elim P Q)) (kw_lrSym_minor_XZ W)
  simp only [map_add, map_sub, map_mul] at hminor
  rw [kw_lrApt_aeval_WP₁ W F hP, kw_lrApt_aeval_WP₂ W F hQ, mul_zero, mul_zero,
    add_zero, sub_eq_zero, kw_lrApt_aeval_lrAdd_Z W F P Q,
    kw_lrApt_aeval_lrAdd_X W F P Q, mul_neg, mul_neg, neg_inj] at hminor
  simpa only [kw_lrSym_vec, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Projective.addXYZ_Z, Projective.addXYZ_X] using hminor

theorem kw_lrApt_aeval_minor_YZ {P Q : Fin 3 → F}
    (hP : (W_F).Equation P) (hQ : (W_F).Equation Q) :
    aeval (Sum.elim P Q) (kw_lrSym_vec W 1) * (W_F).addXYZ P Q 2
      = aeval (Sum.elim P Q) (kw_lrSym_vec W 2) * (W_F).addXYZ P Q 1 := by
  have hminor := congrArg (aeval (R := R) (Sum.elim P Q)) (kw_lrSym_minor_YZ W)
  simp only [map_add, map_sub, map_mul] at hminor
  rw [kw_lrApt_aeval_WP₁ W F hP, kw_lrApt_aeval_WP₂ W F hQ, mul_zero, mul_zero,
    add_zero, sub_eq_zero, kw_lrApt_aeval_lrAdd_Z W F P Q,
    kw_lrApt_aeval_lrAdd_Y W F P Q, mul_neg, mul_neg, neg_inj] at hminor
  simpa only [kw_lrSym_vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Projective.addXYZ_Z, Projective.addXYZ_Y] using hminor

theorem kw_lrApt_aeval_lrSym_smulL (Q : Fin 3 → F) (u : F) (m : Fin 3) :
    aeval (Sum.elim (u • Q) Q) (kw_lrSym_vec W m)
      = u ^ 2 * aeval (Sum.elim Q Q) (kw_lrSym_vec W m) := by
  have hfun : (Sum.elim (u • Q) Q : Fin 3 ⊕ Fin 3 → F)
      = (fun i => u ^ kw_lrBihom_wL i * Sum.elim Q Q i) := by
    funext i; cases i with
    | inl m => simp [kw_lrBihom_wL, Sum.elim_inl, pow_one, Pi.smul_apply, smul_eq_mul]
    | inr m => simp [kw_lrBihom_wL, Sum.elim_inr, pow_zero, one_mul]
  have hw2 : ∀ m, (kw_lrSym_vec W m).IsWeightedHomogeneous kw_lrBihom_wL 2 := by
    intro m; fin_cases m
    · exact kw_lrSymBihom_lrSymX_wL W
    · exact kw_lrSymBihom_lrSymY_wL W
    · exact kw_lrSymBihom_lrSymZ_wL W
  rw [hfun]
  exact kw_lrApt_aeval_weighted_scaling kw_lrBihom_wL (hw2 m) u (Sum.elim Q Q)

private theorem kw_lrApt_sixUClass_liftToE_over_local (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l))) :
    (Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.lift (kw_lrSixU W i j l)
          (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
        ≫ kw_lrSixU_toE W i j l) ≫ π
      = t_F := by
  have hring : ((IsLocalization.Away.lift (kw_lrSixU W i j l)
        (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu).comp
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (kw_lrSixU W i j l)))).comp
        (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)))
      = algebraMap R F := by
    rw [IsLocalization.Away.lift_comp]
    exact (Algebra.TensorProduct.productMap ψᵢ ψⱼ).comp_algebraMap
  rw [Category.assoc, kw_lrSixU_toE_over]
  show Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ((𝒜 i) ⊗[R] (𝒜 j))
      (Localization.Away (kw_lrSixU W i j l)))) ≫ _
    = Spec.map (CommRingCat.ofHom (algebraMap R F))
  rw [← hring]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

include hΔ in

theorem kw_lrApt_sixU_class_eq_addMap (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l))) :
    kw_lrApt_toPointClass W F
        ⟨Spec.map (CommRingCat.ofHom
            (IsLocalization.Away.lift (kw_lrSixU W i j l)
              (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l,
         kw_lrApt_sixUClass_liftToE_over_local W F i j ψᵢ ψⱼ l hu⟩
      = (W_F).addMap ⟦kw_lrApt_chartEval W F i ψᵢ⟧ ⟦kw_lrApt_chartEval W F j ψⱼ⟧ := by
  set P := kw_lrApt_chartEval W F i ψᵢ with hPdef
  set Q := kw_lrApt_chartEval W F j ψⱼ with hQdef
  have hPeq : (W_F).Equation P := kw_lrApt_chartEval_equation W F i ψᵢ
  have hQeq : (W_F).Equation Q := kw_lrApt_chartEval_equation W F j ψⱼ
  have hPnz : P ≠ 0 := kw_lrApt_chartEval_ne_zero W F i ψᵢ
  have hQnz : Q ≠ 0 := kw_lrApt_chartEval_ne_zero W F j ψⱼ
  have hPns : (W_F).Nonsingular P :=
    kw_lrApt_nonsingular_of_equation_of_ne_zero W hΔ hPeq hPnz
  have hQns : (W_F).Nonsingular Q :=
    kw_lrApt_nonsingular_of_equation_of_ne_zero W hΔ hQeq hQnz
  rw [Projective.addMap_eq]
  cases l with
  | inl k =>
    have haddknz : (W_F).addXYZ P Q k ≠ 0 := by
      have hthis := kw_lrApt_psiTens_sixU W F i j ψᵢ ψⱼ (Sum.inl k)
      rw [Sum.elim_inl, kw_lrApt_aeval_lrAdd_vec W F P Q k] at hthis
      exact neg_ne_zero.mp (isUnit_iff_ne_zero.mp (hthis ▸ hu))
    have haddnz : (W_F).addXYZ P Q ≠ 0 := fun h => haddknz (congrFun h k)
    have hnequiv : ¬ P ≈ Q := by
      rintro ⟨u, huQ⟩
      apply haddnz
      have hP' : P = (u : F) • Q := huQ ▸ (Units.smul_def u Q)
      have h := (W_F).addXYZ_smul Q Q (u : F) 1
      rw [one_smul, Projective.addXYZ_self] at h
      rw [hP', h]
      ext n; fin_cases n <;> simp [Pi.smul_apply, smul_eq_mul, mul_zero]
    rw [Projective.add_of_not_equiv hnequiv]
    obtain ⟨ψres, hresFac, hresEval⟩ := kw_lrApt_chartEval_inl W F i j ψᵢ ψⱼ k hu
    have hLHS : kw_lrApt_toPointClass W F
        ⟨_, kw_lrApt_sixUClass_liftToE_over_local W F i j ψᵢ ψⱼ (Sum.inl k) hu⟩
        = ⟦kw_lrApt_chartEval W F k ψres⟧ :=
      kw_lrApt_toPointClass_eq_of_fac W F _ k ψres hresFac
    rw [hLHS]
    have hsmul : kw_lrApt_chartEval W F k ψres
        = (-(W_F).addXYZ P Q k)⁻¹ • (fun m => -(W_F).addXYZ P Q m) := by
      funext m
      rw [hresEval m, Pi.smul_apply, smul_eq_mul, eq_comm, inv_mul_eq_div]
    rw [hsmul,
      show (fun m => -(W_F).addXYZ P Q m) = (-1 : F) • (W_F).addXYZ P Q from
        funext fun m => by rw [Pi.smul_apply, smul_eq_mul, neg_one_mul],
      smul_smul,
      Projective.smul_eq _ (isUnit_iff_ne_zero.mpr
        (mul_ne_zero (inv_ne_zero (neg_ne_zero.mpr haddknz)) (neg_ne_zero.mpr one_ne_zero)))]
  | inr k =>
    have hsymDknz : aeval (Sum.elim P Q) (kw_lrSym_vec W k) ≠ 0 := by
      have hthis := kw_lrApt_psiTens_sixU W F i j ψᵢ ψⱼ (Sum.inr k)
      rw [Sum.elim_inr] at hthis
      exact isUnit_iff_ne_zero.mp (hthis ▸ hu)
    obtain ⟨ψres, hresFac, hresEval⟩ := kw_lrApt_chartEval_inr W F i j ψᵢ ψⱼ k hu
    have hLHS : kw_lrApt_toPointClass W F
        ⟨_, kw_lrApt_sixUClass_liftToE_over_local W F i j ψᵢ ψⱼ (Sum.inr k) hu⟩
        = ⟦kw_lrApt_chartEval W F k ψres⟧ :=
      kw_lrApt_toPointClass_eq_of_fac W F _ k ψres hresFac
    rw [hLHS]
    set symDPQ : Fin 3 → F := fun m => aeval (Sum.elim P Q) (kw_lrSym_vec W m) with hsymDdef
    have hsmul : kw_lrApt_chartEval W F k ψres = (symDPQ k)⁻¹ • symDPQ :=
      funext fun m => (hresEval m).trans (by rw [Pi.smul_apply, smul_eq_mul, inv_mul_eq_div])
    have hsymDPQE : (W_F).Equation symDPQ :=
      (Projective.equation_smul symDPQ (isUnit_iff_ne_zero.mpr (inv_ne_zero hsymDknz))).mp
        (hsmul ▸ kw_lrApt_chartEval_equation W F k ψres)
    have hsymDPQnz : symDPQ ≠ 0 := fun h => hsymDknz (congrFun h k)
    rw [hsmul, Projective.smul_eq _ (isUnit_iff_ne_zero.mpr (inv_ne_zero hsymDknz))]
    by_cases hequiv : P ≈ Q
    · rw [Projective.add_of_equiv hequiv]
      have hdblns : (W_F).Nonsingular ((W_F).dblXYZ P) := by
        have := Projective.nonsingular_add hPns hQns
        rwa [Projective.add_of_equiv hequiv] at this
      have hdblnz : (W_F).dblXYZ P ≠ 0 := kw_lrApt_ne_zero_of_nonsingular W F hdblns
      obtain ⟨u, huQ⟩ := hequiv

      have hscal : symDPQ
          = (u : F) ^ 2 • (fun m => aeval (Sum.elim Q Q) (kw_lrSym_vec W m)) := by
        funext m
        simp only [hsymDdef, Pi.smul_apply, smul_eq_mul]
        rw [show P = (u : F) • Q from huQ ▸ (Units.smul_def u Q)]
        exact kw_lrApt_aeval_lrSym_smulL W F Q (u : F) m
      rw [hscal, Projective.smul_eq _ (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 u.ne_zero))]

      have hdblPQ : (⟦(W_F).dblXYZ P⟧ : Projective.PointClass F) = ⟦(W_F).dblXYZ Q⟧ := by
        rw [show P = (u : F) • Q from huQ ▸ (Units.smul_def u Q),
          Projective.dblXYZ_smul, Projective.smul_eq _ (isUnit_iff_ne_zero.mpr
            (pow_ne_zero 4 u.ne_zero))]
      rw [hdblPQ]

      set symDQQ : Fin 3 → F := fun m => aeval (Sum.elim Q Q) (kw_lrSym_vec W m)
      have hdblQnz : (W_F).dblXYZ Q ≠ 0 := fun h => hdblnz (by
        rw [show P = (u : F) • Q from huQ ▸ (Units.smul_def u Q),
          Projective.dblXYZ_smul, h, smul_zero])
      have hdblQeq : (W_F).Equation ((W_F).dblXYZ Q) := by
        have := Projective.nonsingular_add hQns hQns
        rw [Projective.add_of_equiv (Setoid.refl Q)] at this
        exact this.1
      have hsymDQQE : (W_F).Equation symDQQ := by
        rw [show symDQQ = ((u:F)^2)⁻¹ • symDPQ from funext fun m => by
          rw [hscal, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
            inv_mul_cancel_left₀ (pow_ne_zero 2 u.ne_zero)]]
        exact (Projective.equation_smul symDPQ
          (isUnit_iff_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 u.ne_zero)))).mpr hsymDPQE
      have hsymDQQnz : symDQQ ≠ 0 := fun h => hsymDPQnz (by rw [hscal, h, smul_zero])
      have hXZ : symDQQ 0 * (W_F).dblXYZ Q 2 = symDQQ 2 * (W_F).dblXYZ Q 0 := by
        show aeval _ (kw_lrSym_vec W 0) * _ = aeval _ (kw_lrSym_vec W 2) * _
        simp only [kw_lrSym_vec, Projective.dblXYZ_Z, Projective.dblXYZ_X,
          Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        exact kw_lrApt_aeval_lrSym_cross_XZ W F hQeq
      have hYZ : symDQQ 1 * (W_F).dblXYZ Q 2 = symDQQ 2 * (W_F).dblXYZ Q 1 := by
        show aeval _ (kw_lrSym_vec W 1) * _ = aeval _ (kw_lrSym_vec W 2) * _
        simp only [kw_lrSym_vec, Projective.dblXYZ_Z, Projective.dblXYZ_Y,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        exact kw_lrApt_aeval_lrSym_cross_YZ W F hQeq
      exact kw_lrApt_prop_of_cross_zero W F hXZ hYZ hsymDQQE hdblQeq hsymDQQnz hdblQnz
    · rw [Projective.add_of_not_equiv hequiv]
      have haddns : (W_F).Nonsingular ((W_F).addXYZ P Q) := by
        have := Projective.nonsingular_add hPns hQns
        rwa [Projective.add_of_not_equiv hequiv] at this
      have haddnz : (W_F).addXYZ P Q ≠ 0 := kw_lrApt_ne_zero_of_nonsingular W F haddns
      exact kw_lrApt_prop_of_cross_zero W F
        (kw_lrApt_aeval_minor_XZ W F hPeq hQeq)
        (kw_lrApt_aeval_minor_YZ W F hPeq hQeq)
        hsymDPQE haddns.1 hsymDPQnz haddnz

end MapMulRaw

end WeierstrassProjModel

open _root_.WeierstrassProjModel _root_.P2MW.S_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero.WeierstrassProjModel CategoryTheory AlgebraicGeometry in
attribute [local instance] MvPolynomial.gradedAlgebra in
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra in
set_option maxHeartbeats 6400000 in
theorem _root_.P2MW.S_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero.solution.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] (hΔ : algebraMap R F W.Δ ≠ 0) (i j : Fin 3)
    (ψᵢ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (ψⱼ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X j : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l)))
    (k : Fin 3) (ψₖ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X k : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : Spec.map (CommRingCat.ofHom
            (IsLocalization.Away.lift (kw_lrSixU W i j l)
              (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l
        = Spec.map (CommRingCat.ofHom ψₖ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k) :
    (⟦kw_lrApt_chartEval W F k ψₖ⟧ : WeierstrassCurve.Projective.PointClass F)
      = (kw_lrApt_WF W F).addMap ⟦kw_lrApt_chartEval W F i ψᵢ⟧ ⟦kw_lrApt_chartEval W F j ψⱼ⟧ := by
  have h1 := kw_lrApt_sixU_class_eq_addMap W F hΔ i j ψᵢ ψⱼ l hu
  have h2 := kw_lrApt_toPointClass_eq_of_fac W F
    ⟨(Spec.map (CommRingCat.ofHom
            (IsLocalization.Away.lift (kw_lrSixU W i j l)
              (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l),
     kw_lrApt_sixUClass_liftToE_over_local W F i j ψᵢ ψⱼ l hu⟩ k ψₖ hfac
  exact h2.symm.trans h1

end
end S_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero
end P2MW
export P2MW.S_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero (solution)

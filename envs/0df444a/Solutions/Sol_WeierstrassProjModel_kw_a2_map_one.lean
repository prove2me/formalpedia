-- Prove2me | solution 1 for WeierstrassProjModel.kw_a2_map_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/13a8b34d-39b9-54bf-b6d3-c09f65ce63aa

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_a2_map_one

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6400000

noncomputable section

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

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

theorem kw_lrApt_gen_self (i : Fin 3) : gen i i = 1 := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [kw_lrChart_gen_val, HomogeneousLocalization.val_one]
  exact Localization.mk_self
    (⟨mk₃ (X i : MvPolynomial (Fin 3) R), 1, pow_one _⟩ : Submonoid.powers _)

theorem kw_lrApt_chartEval_self (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    kw_lrApt_chartEval W F i ψ i = 1 := by
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

  show eval _ (W_F).polynomial = 0
  rw [show (W_F).polynomial = MvPolynomial.map (algebraMap R F) W.toProjective.polynomial
        from Projective.map_polynomial (W' := W.toProjective) (f := algebraMap R F),
    kw_lrApt_eval_chartEval W F i ψ, kw_lrChart_dehom_polynomial W i, map_zero]

section AddZeroSectInline

abbrev kw_lrAddZeroSect_coverE : (projModelCR W.toProjective).OpenCover :=
  (projModelAffineOpenCoverCR R W.toProjective).openCover

set_option quotPrecheck false in
local notation "coverE" => kw_lrAddZeroSect_coverE W

section LocalZeroSect

open MvPolynomial in

noncomputable def kw_lrAddZeroSect_YEvalRingHom : ProjModelRingCR W.toProjective →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![(0 : R), 1, 0]) fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact WeierstrassCurve.Projective.equation_zero

open MvPolynomial in

theorem kw_lrAddZeroSect_YEvalRingHom_mk_X1 :
    kw_lrAddZeroSect_YEvalRingHom W
        (Ideal.Quotient.mk _ (X 1 : MvPolynomial (Fin 3) R)) = 1 := by
  show (MvPolynomial.eval ![(0:R), 1, 0]) (X 1) = 1; simp

noncomputable def kw_lrAddZeroSect_YChartEval : (𝒜 1) →+* R :=
  (IsLocalization.Away.lift (g := kw_lrAddZeroSect_YEvalRingHom W)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))
      (kw_lrAddZeroSect_YEvalRingHom_mk_X1 W ▸ isUnit_one)).comp
    (algebraMap (𝒜 1)
      (Localization.Away
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))))

open MvPolynomial in

theorem kw_lrAddZeroSect_YEvalRingHom_comp_algebraMap :
    (kw_lrAddZeroSect_YEvalRingHom W).comp
        (algebraMap R (ProjModelRingCR W.toProjective)) = RingHom.id R := by
  exact RingHom.ext fun r => by
    show (MvPolynomial.eval ![(0:R), 1, 0]) (C r) = r; exact MvPolynomial.eval_C _

theorem kw_lrAddZeroSect_YChartEval_section :
    (kw_lrAddZeroSect_YChartEval W).comp
      ((HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _).comp
        (algebraMap R (projModelGradingCR W.toProjective 0))) = RingHom.id R := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, RingHom.id_apply, kw_lrAddZeroSect_YChartEval,
    HomogeneousLocalization.algebraMap_apply]
  have hval :
      (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _
          (algebraMap R (projModelGradingCR W.toProjective 0) r)).val
        = algebraMap (ProjModelRingCR W.toProjective)
            (Localization.Away
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))
            (algebraMap R (ProjModelRingCR W.toProjective) r) := rfl
  rw [hval, IsLocalization.Away.lift, IsLocalization.lift_eq]
  exact RingHom.congr_fun (kw_lrAddZeroSect_YEvalRingHom_comp_algebraMap W) r

noncomputable def kw_lrAddZeroSect_zeroMor : Spec (CommRingCat.of R) ⟶ E :=
  Spec.map (CommRingCat.ofHom (kw_lrAddZeroSect_YChartEval W)) ≫
    Proj.awayι (projModelGradingCR W.toProjective) _ (kw_lrChart_mkX_mem_one W 1) one_pos

theorem kw_lrAddZeroSect_zeroMor_over :
    kw_lrAddZeroSect_zeroMor W ≫ π = 𝟙 (Spec (CommRingCat.of R)) := by
  simp only [kw_lrAddZeroSect_zeroMor, projModelStrCR, Category.assoc]
  rw [← Category.assoc (Proj.awayι ..), Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    kw_lrAddZeroSect_YChartEval_section, CommRingCat.ofHom_id, Spec.map_id]

end LocalZeroSect

noncomputable def kw_lrAddZeroSect_YChartEvalₐ : (𝒜 1) →ₐ[R] R :=
  { kw_lrAddZeroSect_YChartEval W with
    commutes' := fun r => RingHom.congr_fun (kw_lrAddZeroSect_YChartEval_section W) r }

theorem kw_lrAddZeroSect_YChartEval_gen (m : Fin 3) :
    kw_lrAddZeroSect_YChartEval W (kw_lrChart_gen W 1 m) = ![(0:R), 1, 0] m := by
  show IsLocalization.Away.lift (g := kw_lrAddZeroSect_YEvalRingHom W)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))
      (kw_lrAddZeroSect_YEvalRingHom_mk_X1 W ▸ isUnit_one) (kw_lrChart_gen W 1 m).val = _
  rw [kw_lrChart_gen_val, Localization.mk_eq_mk', IsLocalization.Away.lift,
    IsLocalization.lift_mk']
  simp only [Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight, RingHom.toMonoidHom_eq_coe,
    MonoidHom.restrict_apply, MonoidHom.coe_coe]
  show (MvPolynomial.eval ![(0:R), 1, 0]) (X m)
    = ![(0:R), 1, 0] m * (MvPolynomial.eval ![(0:R), 1, 0]) (X 1)
  simp

end AddZeroSectInline

section ChartFactorization

theorem kw_lrApt_factor_of_range (φ : SchemeHomOver (t_F) π) (i : Fin 3)
    (hrange : Set.range φ.1 ⊆ Set.range (awayι₃ i)) :
    ∃ ψ : (𝒜 i) →ₐ[R] F,
      φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (coverE).f i := by
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

section MapOne

set_option quotPrecheck false in
local notation "𝒜1" => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X 1 : MvPolynomial (Fin 3) R))

noncomputable def kw_lrApt_YChartEvalF : (𝒜1) →ₐ[R] F :=
  (IsScalarTower.toAlgHom R R F).comp (kw_lrAddZeroSect_YChartEvalₐ W)

theorem kw_lrApt_YChartEvalF_gen (m : Fin 3) :
    kw_lrApt_YChartEvalF W F (kw_lrChart_gen W 1 m) = ![(0:F), 1, 0] m := by
  show (algebraMap R F) (kw_lrAddZeroSect_YChartEval W (kw_lrChart_gen W 1 m)) = _
  rw [kw_lrAddZeroSect_YChartEval_gen]
  fin_cases m <;> simp

theorem kw_lrApt_chartEval_YChartEvalF :
    kw_lrApt_chartEval W F 1 (kw_lrApt_YChartEvalF W F) = ![(0:F), 1, 0] :=
  funext fun m => kw_lrApt_YChartEvalF_gen W F m

theorem kw_lrApt_G_one_fac :
    (t_F) ≫ (kwZeroSect R W).1
      = Spec.map (CommRingCat.ofHom (kw_lrApt_YChartEvalF W F).toRingHom)
          ≫ (coverE).f (1 : Fin 3) := by

  have hzm : kw_lrAddZeroSect_zeroMor W = (kwZeroSect R W).1 := rfl
  rw [← hzm, kw_lrAddZeroSect_zeroMor,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end MapOne

end

theorem solution.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] (k : Fin 3)
    (ψₖ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X k : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : (kw_lrAptb_tF (R := R) F) ≫ (kwZeroSect R W).1
      = Spec.map (CommRingCat.ofHom ψₖ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k) :
    (⟦kw_lrApt_chartEval W F k ψₖ⟧ : WeierstrassCurve.Projective.PointClass F)
      = ⟦![(0:F), 1, 0]⟧ := by
  have h1 := kw_lrApt_toPointClass_eq_of_fac W F
    ⟨(kw_lrAptb_tF (R := R) F) ≫ (kwZeroSect R W).1,
      by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id]⟩ k ψₖ hfac
  have h2 := kw_lrApt_toPointClass_eq_of_fac W F
    ⟨(kw_lrAptb_tF (R := R) F) ≫ (kwZeroSect R W).1,
      by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id]⟩ 1 (kw_lrApt_YChartEvalF W F)
    (kw_lrApt_G_one_fac W F)
  rw [← h1, h2, kw_lrApt_chartEval_YChartEvalF]

end S_WeierstrassProjModel_kw_a2_map_one
end P2MW
export P2MW.S_WeierstrassProjModel_kw_a2_map_one (solution)

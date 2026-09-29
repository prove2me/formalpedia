-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_mul_of_eval_prePsi_eq_zero_of_nsmul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/01e78a05-1429-5ab5-9c78-e86f8b3cd45f

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_relabel_eq_relabel_map
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_mul_of_eval_prePsi_eq_zero_of_nsmul_eq_one
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

namespace LAGeneric

theorem isSectionThrough_of_range_subset {T : Type} [CommRing T] (W : WeierstrassCurve.Projective T) (R : Section W)
    (h : Set.range R.1.base ⊆ Set.range (zChartι W).base) : ∃ x y : T, IsSectionThrough R x y := by
  let g : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (ZChartRing W)) := IsOpenImmersion.lift (zChartι W) R.1 h
  have hg : g ≫ zChartι W = R.1 := IsOpenImmersion.lift_fac _ _ _
  refine ⟨(Spec.preimage g).hom (xOverZ W), (Spec.preimage g).hom (yOverZ W), (Spec.preimage g).hom, ?_, rfl, rfl⟩
  show R.1 = Spec.map (CommRingCat.ofHom (Spec.preimage g).hom) ≫ zChartι W
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]

theorem range_subset_of_forall_isMaximal {T : Type} [CommRing T] {X : Scheme} (r : Spec (CommRingCat.of T) ⟶ X) (U : X.Opens)
    (h : ∀ (𝔪 : Ideal T) (h𝔪 : 𝔪.IsMaximal), r.base ((⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum T)) ∈ (U : Set X)) :
    Set.range r.base ⊆ (U : Set X) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨𝔪, h𝔪, hz𝔪⟩ := Ideal.exists_le_maximal z.asIdeal z.isPrime.ne_top
  have hspec : z ⤳ (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum T) :=
    (PrimeSpectrum.le_iff_specializes z ⟨𝔪, h𝔪.isPrime⟩).mp hz𝔪
  have hspec' : r.base z ⤳ r.base ⟨𝔪, h𝔪.isPrime⟩ := hspec.map r.base.hom.continuous
  by_contra hz
  have hclosed : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  exact (hspec'.mem_closed hclosed hz) (h 𝔪 h𝔪)

theorem exists_specMap_quotient_apply_eq {T : Type} [CommRing T] (𝔪 : Ideal T) (h𝔪 : 𝔪.IsMaximal) :
    ∃ y : Spec (CommRingCat.of (T ⧸ 𝔪)),
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))).base y = (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum T) := by
  haveI := h𝔪.isPrime
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (T ⧸ 𝔪)), ?_⟩
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk 𝔪) ⊥ = 𝔪
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

end LAGeneric

namespace LAAux

theorem zlinComb_eq_of_one_eq {T : Type} [CommRing T] (W : WeierstrassCurve.Projective T) [W.toAffine.IsElliptic]
    (G₀ G₁ : RelativeGroupLaw T (projModelStrCR W))
    (h1 : (G₀.one (𝟙 _)).1 = (G₁.one (𝟙 _)).1) (P Q : Section W) (a b : ℤ) :
    zlinComb G₀ P Q a b = zlinComb G₁ P Q a b := by
  have hmul : ∀ x y : Section W, G₀.mul (𝟙 _) x y = G₁.mul (𝟙 _) x y :=
    fun x y => RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic W G₀ G₁ h1 (𝟙 _) x y
  have hone : G₀.one (𝟙 (base (T := T))) = G₁.one (𝟙 _) := Subtype.ext h1
  have hnsmul : ∀ (n : ℕ) (x : Section W), G₀.nsmul (𝟙 _) n x = G₁.nsmul (𝟙 _) n x := by
    intro n x
    induction n with
    | zero => exact hone
    | succ n ih => rw [G₀.nsmul_succ, G₁.nsmul_succ, ih, hmul]
  have hinv : ∀ x : Section W, G₀.inv (𝟙 _) x = G₁.inv (𝟙 _) x := by
    intro x
    letI := G₁.pointGroup (𝟙 (base (T := T)))
    have h : G₀.inv (𝟙 _) x * x = 1 := by
      show G₁.mul (𝟙 _) (G₀.inv (𝟙 _) x) x = G₁.one (𝟙 _)
      rw [← hmul, G₀.inv_mul_cancel, hone]
    exact eq_inv_of_mul_eq_one_left h
  have hz : ∀ (n : ℤ) (x : Section W), zsmulSection G₀ n x = zsmulSection G₁ n x := by
    intro n x
    cases n with
    | ofNat k => exact hnsmul k x
    | negSucc k =>
      show G₀.inv _ (G₀.nsmul _ (k + 1) x) = G₁.inv _ (G₁.nsmul _ (k + 1) x)
      rw [hnsmul, hinv]
  show G₀.mul _ (zsmulSection G₀ a P) (zsmulSection G₀ b Q) = G₁.mul _ (zsmulSection G₁ a P) (zsmulSection G₁ b Q)
  rw [hz, hz, hmul]

theorem exists_isSectionThrough_comb_one_one_field
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (q : ℕ) [Fact q.Prime] (hℓq : ℓ ≠ q)
    {T : Type} [Field T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S P : Section W) (x₀ y₀ : T) (hS : IsSectionThrough S x₀ y₀) (hx0 : (W.preΨ ℓ).eval x₀ = 0)
    (hP : (𝒢 T W hΔ).nsmul _ q P = (𝒢 T W hΔ).one _) :
    ∃ u v : T, IsSectionThrough (zlinComb (𝒢 T W hΔ) S P 1 1) u v := by
  classical
  haveI : W.toAffine.IsElliptic := ⟨hΔ⟩
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
  have hG1 : ((𝒢 T W hΔ).one (𝟙 _)).1 = (kwZeroSect T W).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢 T W hΔ)).mp
      (h𝒢O T W hΔ)
  obtain ⟨ev, hev, -, hcoord⟩ :=
    WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain W (𝒢 T W hΔ) hG1
  set ι : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of T) := Spec.map (CommRingCat.ofHom (algebraMap T T)) with hι
  have hι1 : ι = 𝟙 _ := by rw [hι, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hψ : ι ≫ 𝟙 (Spec (CommRingCat.of T)) = ι := Category.comp_id _
  have hmul : ∀ P Q : Section W,
      ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).mul _ P Q)) =
        ev T (schemeHomOverComp ι hψ P) + ev T (schemeHomOverComp ι hψ Q) := by
    intro P Q
    rw [(𝒢 T W hΔ).mul_natural (𝟙 _) ι ι hψ P Q]
    exact hev.1 T _ _
  have hone : ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).one _)) = 0 := by
    have h := hmul ((𝒢 T W hΔ).one _) ((𝒢 T W hΔ).one _)
    rw [(𝒢 T W hΔ).one_mul] at h
    have h2 : ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).one _)) + ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).one _)) =
        ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).one _)) + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hnsmul : ∀ (k : ℕ) (P : Section W),
      ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).nsmul _ k P)) = k • ev T (schemeHomOverComp ι hψ P) := by
    intro k P
    induction k with
    | zero => rw [RelativeGroupLaw.nsmul_zero, zero_smul]; exact hone
    | succ k ih => rw [RelativeGroupLaw.nsmul_succ, hmul, ih, add_smul, one_smul]
  have hread : ∀ (P : Section W) (u v : T), IsSectionThrough P u v →
      ∃ h : W.toAffine.Nonsingular u v, ev T (schemeHomOverComp ι hψ P) = WeierstrassCurve.Affine.Point.some u v h := by
    intro P u v hPuv
    obtain ⟨χ, hχ, hu, hv⟩ := hPuv
    have hfac : (schemeHomOverComp ι hψ P).1 =
        Spec.map (CommRingCat.ofHom ((algebraMap T T).comp χ)) ≫ zChartι W := by
      rw [schemeHomOverComp_coe, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      show ι ≫ P.1 = ι ≫ _
      rw [hχ]
    obtain ⟨hxy, he⟩ := hcoord T (schemeHomOverComp ι hψ P) ((algebraMap T T).comp χ) hfac
    have hu' : ((algebraMap T T).comp χ) (xOverZ W) = u := by rw [RingHom.comp_apply, Algebra.algebraMap_self_apply]; exact hu
    have hv' : ((algebraMap T T).comp χ) (yOverZ W) = v := by rw [RingHom.comp_apply, Algebra.algebraMap_self_apply]; exact hv
    refine ⟨?_, ?_⟩
    · have h := hxy; rw [hu', hv'] at h; exact h
    · rw [he]
      congr 1
  have hinj : ∀ P Q : Section W, schemeHomOverComp ι hψ P = schemeHomOverComp ι hψ Q → P = Q := by
    intro P Q h
    have h1 := congrArg Subtype.val h
    rw [schemeHomOverComp_coe, schemeHomOverComp_coe, hι1, Category.id_comp, Category.id_comp] at h1
    exact Subtype.ext h1
  obtain ⟨hxy, heS⟩ := hread S x₀ y₀ hS
  have tS : ℓ • WeierstrassCurve.Affine.Point.some _ _ hxy = 0 := by
    have hx := hx0
    rw [WeierstrassCurve.preΨ_ofNat] at hx
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd hxy).mpr hx
  have hS0 : WeierstrassCurve.Affine.Point.some _ _ hxy ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hordS : addOrderOf (WeierstrassCurve.Affine.Point.some _ _ hxy) = ℓ := addOrderOf_eq_prime_iff.mpr ⟨tS, hS0⟩
  have hqP : q • ev T (schemeHomOverComp ι hψ P) = 0 := by
    rw [← hnsmul, hP, hone]
  have hsum_ne : ev T (schemeHomOverComp ι hψ S) + ev T (schemeHomOverComp ι hψ P) ≠ 0 := by
    intro h0
    have hPe : ev T (schemeHomOverComp ι hψ P) = -(WeierstrassCurve.Affine.Point.some _ _ hxy) := by
      rw [← heS]; exact (neg_eq_of_add_eq_zero_right h0).symm
    have hqS : q • WeierstrassCurve.Affine.Point.some _ _ hxy = 0 := by
      have h1 : q • (ev T (schemeHomOverComp ι hψ S) + ev T (schemeHomOverComp ι hψ P)) = 0 := by
        rw [h0, nsmul_zero]
      rwa [nsmul_add, hqP, add_zero, heS] at h1
    have hdvd : ℓ ∣ q := by rw [← hordS]; exact addOrderOf_dvd_of_nsmul_eq_zero hqS
    exact hℓq ((Nat.prime_dvd_prime_iff_eq hp (Fact.out)).mp hdvd)
  have hval : ev T (schemeHomOverComp ι hψ (zlinComb (𝒢 T W hΔ) S P 1 1)) =
      ev T (schemeHomOverComp ι hψ S) + ev T (schemeHomOverComp ι hψ P) := by
    show ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).mul _ ((𝒢 T W hΔ).nsmul _ 1 S) ((𝒢 T W hΔ).nsmul _ 1 P))) = _
    rw [hmul, hnsmul, hnsmul, one_smul, one_smul]
  rcases hh : ev T (schemeHomOverComp ι hψ S) + ev T (schemeHomOverComp ι hψ P) with _ | ⟨xr, yr, hr⟩
  · exact absurd (hh.trans WeierstrassCurve.Affine.Point.zero_def.symm) hsum_ne
  · obtain ⟨Sr, hSr⟩ := ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 xr yr).mp hr.left
    obtain ⟨hxyr, heSr⟩ := hread Sr xr yr hSr
    have hh' : ev T (schemeHomOverComp ι hψ S) + ev T (schemeHomOverComp ι hψ P) =
        WeierstrassCurve.Affine.Point.some xr yr hxyr := hh
    have heq : zlinComb (𝒢 T W hΔ) S P 1 1 = Sr := by
      apply hinj
      apply (ev T).injective
      rw [hval, hh', heSr]
    exact ⟨xr, yr, heq ▸ hSr⟩

universe u in

theorem range_subset_of_sq {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T)
    (f : T →+* T') (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    {W' : WeierstrassCurve.Projective T'} (hc : W' = W.map f) (S' : Section W') (x' y' : T')
    (hS' : IsSectionThrough S' x' y') (p : Spec (CommRingCat.of T) ⟶ projModelCR W)
    (hsq : S'.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom f) ≫ p) :
    Set.range (Spec.map (CommRingCat.ofHom f) ≫ p).base ⊆
      (Proj.basicOpen (projModelGradingCR W) (coord W 2) : Set _) := by
  subst hc
  rw [eqToHom_refl, Category.id_comp] at hsq
  obtain ⟨χ', hsec', -, -⟩ := hS'
  have hsec'' : S'.1 = Spec.map (CommRingCat.ofHom χ') ≫ zChartι (W.map f) := hsec'
  rw [← hsq]
  rintro _ ⟨z, rfl⟩
  have e : φ (coord W 2) = coord (W.map f) 2 := hcoef.2 2
  have h3 : S'.1.base z ∈ (Proj.map φ hφ ⁻¹ᵁ Proj.basicOpen (projModelGradingCR W) (coord W 2) : Set _) := by
    rw [Proj.map_preimage_basicOpen, e]
    have hopen : Set.range (zChartι (W.map f)).base =
        ((Proj.basicOpen (projModelGradingCR (W.map f)) (coord (W.map f) 2)) : Set _) := by
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    rw [← hopen, hsec'']
    exact ⟨(Spec.map (CommRingCat.ofHom χ')).base z, rfl⟩
  exact h3

theorem zlinComb_one_zero {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) : zlinComb G P Q 1 0 = P := by
  show G.mul _ (G.nsmul _ 1 P) (G.nsmul _ 0 Q) = P
  rw [G.nsmul_one_apply, G.nsmul_zero, G.mul_one]

theorem zlinComb_zero_natCast {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) (n : ℕ) : zlinComb G P Q 0 (n : ℤ) = G.nsmul _ n Q := by
  show G.mul _ (G.nsmul _ 0 P) (G.nsmul _ n Q) = _
  rw [G.nsmul_zero, G.one_mul]

theorem zlinComb_one_one {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) : zlinComb G P Q 1 1 = G.mul _ P Q := by
  show G.mul _ (G.nsmul _ 1 P) (G.nsmul _ 1 Q) = _
  rw [G.nsmul_one_apply, G.nsmul_one_apply]

theorem range_fibre_subset_mul
    {A : Type} [CommRing A] (𝒢₀ : GroupLaws A) (h𝒢₀ : 𝒢₀.IsChordTangent) (h𝒢₀O : 𝒢₀.IsOriginIdentity)
    (q₀ : ℕ) (𝒯₀ : LevelTransport A 𝒢₀ q₀) (h𝒯₀ : 𝒯₀.IsSectionTransport)
    (hVC₀ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO₀ : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (q : ℕ) [Fact q.Prime] (hℓq : ℓ ≠ q)
    {T : Type} [CommRing T] [Algebra A T] {k : Type} [Field k] [Algebra A k] (f : T →ₐ[A] k)
    (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (xr yr : T) (hS : IsSectionThrough x.P xr yr) (hx0 : (x.curve.preΨ ℓ).eval xr = 0)
    (hP : (𝒢₀ T x.curve hΔ).nsmul _ q x.Q = (𝒢₀ T x.curve hΔ).one _) :
    Set.range (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ((𝒢₀ T x.curve hΔ).mul _ x.P x.Q).1).base ⊆
      (Proj.basicOpen (projModelGradingCR x.curve) (coord x.curve 2) : Set _) := by
  obtain ⟨hc1, -⟩ := h𝒯₀.2 T k f x
  have hΔk : IsUnit (𝒯₀.map f x).curve.Δ := by rw [hc1, WeierstrassCurve.map_Δ]; exact hΔ.map _
  have hxk : ((𝒯₀.map f x).curve.preΨ ℓ).eval (f xr) = 0 := by
    rw [hc1, WeierstrassCurve.map_preΨ, Polynomial.eval_map, show f xr = f.toRingHom xr from rfl,
      Polynomial.eval₂_at_apply, hx0, map_zero]
  have em : ∀ g : Matrix (Fin 2) (Fin 2) ℤ,
      𝒯₀.map f (RawDrinfeldPair.relabel 𝒢₀ g x hΔ) = RawDrinfeldPair.relabel 𝒢₀ g (𝒯₀.map f x) hΔk :=
    fun g => WeierstrassCurve.DrinfeldGlobal.LevelTransport.map_relabel_eq_relabel_map 𝒢₀ h𝒢₀ h𝒢₀O q₀ 𝒯₀ h𝒯₀ hVC₀ hCO₀
      T k f g x hΔ hΔk

  let g₁ : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 0]
  have hr₁P : (RawDrinfeldPair.relabel 𝒢₀ g₁ x hΔ).P = x.P := by
    show zlinComb _ _ _ (g₁ 0 0) (g₁ 1 0) = _
    exact zlinComb_one_zero _ _ _
  have hr₁Q : (RawDrinfeldPair.relabel 𝒢₀ g₁ x hΔ).Q = x.P := by
    show zlinComb _ _ _ (g₁ 0 1) (g₁ 1 1) = _
    exact zlinComb_one_zero _ _ _
  obtain ⟨tP, -⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport A 𝒢₀ q₀ 𝒯₀ h𝒯₀ f
    (RawDrinfeldPair.relabel 𝒢₀ g₁ x hΔ) (hCO₀ T k f _) ⟨xr, yr, xr, yr⟩
    (by rw [hr₁P]; exact hS) (by rw [hr₁Q]; exact hS)
  have hSk : IsSectionThrough (𝒯₀.map f x).P (f xr) (f yr) := by
    have h := tP
    rw [em g₁] at h
    have e : (RawDrinfeldPair.relabel 𝒢₀ g₁ (𝒯₀.map f x) hΔk).P = (𝒯₀.map f x).P := by
      show zlinComb _ _ _ (g₁ 0 0) (g₁ 1 0) = _
      exact zlinComb_one_zero _ _ _
    rw [e] at h
    exact h

  let gq : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; (q : ℤ), 0]
  let g0 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 0, 0]
  have hrel : RawDrinfeldPair.relabel 𝒢₀ gq x hΔ = RawDrinfeldPair.relabel 𝒢₀ g0 x hΔ := by
    show (⟨x.curve, zlinComb _ x.P x.Q (gq 0 0) (gq 1 0), zlinComb _ x.P x.Q (gq 0 1) (gq 1 1)⟩ : RawDrinfeldPair T) =
      ⟨x.curve, zlinComb _ x.P x.Q (g0 0 0) (g0 1 0), zlinComb _ x.P x.Q (g0 0 1) (g0 1 1)⟩
    have e1 : zlinComb (𝒢₀ T x.curve hΔ) x.P x.Q (gq 0 0) (gq 1 0) = zlinComb (𝒢₀ T x.curve hΔ) x.P x.Q (g0 0 0) (g0 1 0) := by
      show zlinComb (𝒢₀ T x.curve hΔ) x.P x.Q 0 (q : ℤ) = zlinComb (𝒢₀ T x.curve hΔ) x.P x.Q 0 ((0 : ℕ) : ℤ)
      rw [zlinComb_zero_natCast, zlinComb_zero_natCast, hP, RelativeGroupLaw.nsmul_zero]
    rw [e1]
    rfl
  have hPk : (𝒢₀ k (𝒯₀.map f x).curve hΔk).nsmul _ q (𝒯₀.map f x).Q = (𝒢₀ k (𝒯₀.map f x).curve hΔk).one _ := by
    have h := congrArg (𝒯₀.map f) hrel
    rw [em gq, em g0] at h
    have hPm' : HEq (RawDrinfeldPair.relabel 𝒢₀ gq (𝒯₀.map f x) hΔk).P (RawDrinfeldPair.relabel 𝒢₀ g0 (𝒯₀.map f x) hΔk).P := by
      rw [h]
    have hPm : (RawDrinfeldPair.relabel 𝒢₀ gq (𝒯₀.map f x) hΔk).P = (RawDrinfeldPair.relabel 𝒢₀ g0 (𝒯₀.map f x) hΔk).P :=
      eq_of_heq hPm'
    have e1 : (RawDrinfeldPair.relabel 𝒢₀ gq (𝒯₀.map f x) hΔk).P =
        (𝒢₀ k (𝒯₀.map f x).curve hΔk).nsmul _ q (𝒯₀.map f x).Q := by
      show zlinComb _ _ _ 0 (q : ℤ) = _
      exact zlinComb_zero_natCast _ _ _ q
    have e2 : (RawDrinfeldPair.relabel 𝒢₀ g0 (𝒯₀.map f x) hΔk).P = (𝒢₀ k (𝒯₀.map f x).curve hΔk).one _ := by
      show zlinComb _ _ _ 0 ((0 : ℕ) : ℤ) = _
      rw [zlinComb_zero_natCast, RelativeGroupLaw.nsmul_zero]
    rw [e1, e2] at hPm
    exact hPm

  obtain ⟨u, v, hthr⟩ := exists_isSectionThrough_comb_one_one_field A 𝒢₀ h𝒢₀ h𝒢₀O ℓ hℓ3 q hℓq
    (𝒯₀.map f x).curve hΔk (𝒯₀.map f x).P (𝒯₀.map f x).Q (f xr) (f yr) hSk hxk hPk

  let g₁₁ : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 0]
  have hRk' : IsSectionThrough (𝒯₀.map f (RawDrinfeldPair.relabel 𝒢₀ g₁₁ x hΔ)).P u v := by
    rw [em g₁₁]
    show IsSectionThrough (zlinComb _ _ _ (g₁₁ 0 0) (g₁₁ 1 0)) u v
    exact hthr

  obtain ⟨φ, hφ, hcoef⟩ := hCO₀ T k f x.curve
  obtain ⟨hc2, hsq2⟩ := h𝒯₀.2 T k f (RawDrinfeldPair.relabel 𝒢₀ g₁₁ x hΔ)
  obtain ⟨hsqP, -⟩ := hsq2 φ hφ hcoef
  have key := range_subset_of_sq x.curve f.toRingHom φ hφ hcoef hc2 _ u v hRk' _ hsqP
  have eR : (RawDrinfeldPair.relabel 𝒢₀ g₁₁ x hΔ).P = (𝒢₀ T x.curve hΔ).mul _ x.P x.Q := by
    show zlinComb _ _ _ (g₁₁ 0 0) (g₁₁ 1 0) = _
    exact zlinComb_one_one _ _ _
  rw [← eR]
  exact key

end LAAux

open LAAux in

theorem solution
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (q : ℕ) [Fact q.Prime] (hℓq : ℓ ≠ q)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) (hx : (W.preΨ ℓ).eval x = 0)
    (P : Section W) (hP : (𝒢 T W hΔ).nsmul _ q P = (𝒢 T W hΔ).one _) :
    ∃ x' y' : T, IsSectionThrough ((𝒢 T W hΔ).mul _ S P) x' y' := by
  haveI : W.toAffine.IsElliptic := ⟨hΔ⟩
  obtain ⟨𝒢₀, 𝒯₀, h𝒢₀, h𝒢₀O, h𝒯₀, hVC₀, hCO₀⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport A ℓ

  have h1 : ((𝒢 T W hΔ).one (𝟙 _)).1 = ((𝒢₀ T W hΔ).one (𝟙 _)).1 := by
    rw [(RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢 T W hΔ)).mp (h𝒢O T W hΔ),
      (RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢₀ T W hΔ)).mp (h𝒢₀O T W hΔ)]
  have hmulEq : ∀ a b : Section W, (𝒢 T W hΔ).mul (𝟙 _) a b = (𝒢₀ T W hΔ).mul (𝟙 _) a b :=
    fun a b => RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic W _ _ h1 (𝟙 _) a b
  have honeEq : (𝒢 T W hΔ).one (𝟙 (base (T := T))) = (𝒢₀ T W hΔ).one (𝟙 _) := Subtype.ext h1
  have hnsmulEq : ∀ (n : ℕ) (a : Section W), (𝒢 T W hΔ).nsmul (𝟙 _) n a = (𝒢₀ T W hΔ).nsmul (𝟙 _) n a := by
    intro n a
    induction n with
    | zero => exact honeEq
    | succ n ih => rw [(𝒢 T W hΔ).nsmul_succ, (𝒢₀ T W hΔ).nsmul_succ, ih, hmulEq]
  have hP₀ : (𝒢₀ T W hΔ).nsmul _ q P = (𝒢₀ T W hΔ).one _ := by rw [← hnsmulEq, hP, honeEq]
  rw [hmulEq]

  apply LAGeneric.isSectionThrough_of_range_subset
  rw [show Set.range (zChartι W).base = ((Proj.basicOpen (projModelGradingCR W) (coord W 2)) : Set _) from by
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]]
  apply LAGeneric.range_subset_of_forall_isMaximal
  intro 𝔪 h𝔪
  letI : Field (T ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  obtain ⟨y_1, hy⟩ := LAGeneric.exists_specMap_quotient_apply_eq 𝔪 h𝔪
  have hfib := range_fibre_subset_mul 𝒢₀ h𝒢₀ h𝒢₀O ℓ 𝒯₀ h𝒯₀ hVC₀ hCO₀ ℓ hℓ3 q hℓq (Ideal.Quotient.mkₐ A 𝔪)
    (⟨W, S, P⟩ : RawDrinfeldPair T) hΔ x y hS hx hP₀ ⟨y_1, rfl⟩
  rw [← hy]
  exact hfib

end

end S_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_mul_of_eval_prePsi_eq_zero_of_nsmul_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_mul_of_eval_prePsi_eq_zero_of_nsmul_eq_one (solution)

-- Prove2me | solution 1 for WeierstrassCurve.exists_specializationHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/28b888b7-9fad-5ea1-ad33-bb957e38f4c0

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Definitions.Def_EllipticCurve_PointReduction
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Definitions.Def_FieldTheory_RatFuncTower
import Theorems.Thm_WeierstrassCurve_reducePoint_add
import Theorems.Thm_WeierstrassCurve_reducePoint_some
import Theorems.Thm_WeierstrassCurve_reducePoint_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_specializationHom
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point RubinSilverberg
open scoped Classical

open RatFuncTower

namespace CAlpha

abbrev Qbar : Type := AlgebraicClosure ℚ
abbrev A : Type := Polynomial Qbar
abbrev ι : ℚ →+* Qbar := algebraMap ℚ Qbar

variable (t₀ : ℚ)

abbrev P : Ideal A := Ideal.span {X - C (ι t₀)}

scoped instance P_isMaximal : (P t₀).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X_sub_C _)

theorem P_ne_bot : P t₀ ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_sub_C_ne_zero _

theorem mem_P_iff (g : A) : g ∈ P t₀ ↔ g.eval (ι t₀) = 0 := by
  rw [Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot, IsRoot.def]

abbrev R : Type := Localization.AtPrime (P t₀)

scoped instance R_isDVR : IsDiscreteValuationRing (R t₀) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A (P_ne_bot t₀) _

def resIso : IsLocalRing.ResidueField (R t₀) ≃+* Qbar :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal (P t₀) (R t₀)).symm.trans
    (Polynomial.quotientSpanXSubCAlgEquiv (ι t₀)).toRingEquiv

theorem resIso_residue_algebraMap (f : A) :
    resIso t₀ (IsLocalRing.residue (R t₀) (algebraMap A (R t₀) f)) = f.eval (ι t₀) := by
  show ((IsLocalization.AtPrime.equivQuotMaximalIdeal (P t₀) (R t₀)).symm.trans
    (Polynomial.quotientSpanXSubCAlgEquiv (ι t₀)).toRingEquiv)
      (Ideal.Quotient.mk _ (algebraMap A (R t₀) f)) = _
  rw [RingEquiv.trans_apply, ← IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk (P t₀) (R t₀) f,
    RingEquiv.symm_apply_apply]
  exact Polynomial.quotientSpanXSubCAlgEquiv_mk _ _

theorem resIso_residue_X : resIso t₀ (IsLocalRing.residue (R t₀) (algebraMap A (R t₀) X)) = ι t₀ := by
  rw [resIso_residue_algebraMap, eval_X]

theorem resIso_residue_C (c : Qbar) :
    resIso t₀ (IsLocalRing.residue (R t₀) (algebraMap A (R t₀) (C c))) = c := by
  rw [resIso_residue_algebraMap, eval_C]

theorem algebraMap_mem_maximalIdeal_iff (g : A) :
    algebraMap A (R t₀) g ∈ IsLocalRing.maximalIdeal (R t₀) ↔ g.eval (ι t₀) = 0 := by
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (R t₀) (P t₀) g, mem_P_iff]

scoped instance : CharZero (IsLocalRing.ResidueField (R t₀)) :=
  (resIso t₀).toRingHom.charZero_iff (resIso t₀).injective |>.mpr inferInstance

example : Algebra (R t₀) K0 := inferInstance
example : IsScalarTower A (R t₀) K0 := inferInstance
example : IsFractionRing (R t₀) K0 := inferInstance
example : Algebra (Polynomial ℚ) K0 := inferInstance

abbrev ιX : Polynomial ℚ →+* A := Polynomial.mapRingHom ι

abbrev ψR : Polynomial ℚ →+* R t₀ := (algebraMap A (R t₀)).comp ιX

theorem algebraMap_R_K0_ψR (p : Polynomial ℚ) : algebraMap (R t₀) K0 (ψR t₀ p) = algebraMap (Polynomial ℚ) K0 p := by
  rw [algebraMap_ratPoly_apply]; exact (IsScalarTower.algebraMap_apply A (R t₀) K0 _).symm

variable (σ : Qbar ≃ₐ[ℚ] Qbar)

abbrev σA : A ≃ₐ[ℚ] A := Polynomial.mapAlgEquiv σ

theorem σA_apply (f : A) : σA σ f = f.map (σ : Qbar →+* Qbar) := rfl

theorem σ_ι (q : ℚ) : σ (ι q) = ι q := σ.commutes q

theorem ringHom_ext_K0 {S : Type*} [CommRing S] {j k : K0 →+* S}
    (h : ∀ f : A, j (algebraMap A K0 f) = k (algebraMap A K0 f)) : j = k :=
  IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext h)

theorem σA_gen : σA σ (X - C (ι t₀)) = X - C (ι t₀) := by
  rw [σA_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe, σ_ι]

theorem mem_P_σA_iff (g : A) : σA σ g ∈ P t₀ ↔ g ∈ P t₀ := by
  constructor
  · intro h
    rw [Ideal.mem_span_singleton] at h ⊢
    have := map_dvd (σA σ).symm h
    rwa [← σA_gen t₀ σ, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply] at this
  · intro h
    rw [Ideal.mem_span_singleton] at h ⊢
    have := map_dvd (σA σ) h
    rwa [σA_gen] at this

theorem primeCompl_map_σA :
    (P t₀).primeCompl.map (σA σ).toRingEquiv.toMonoidHom = (P t₀).primeCompl := by
  ext g
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact fun h => hg' ((mem_P_σA_iff t₀ σ g').mp h)
  · intro hg
    refine ⟨(σA σ).symm g, fun h => hg ?_, (σA σ).apply_symm_apply g⟩
    have := (mem_P_σA_iff t₀ σ ((σA σ).symm g)).mpr h
    rwa [AlgEquiv.apply_symm_apply] at this

def σR : R t₀ ≃+* R t₀ :=
  IsLocalization.ringEquivOfRingEquiv (R t₀) (R t₀) (σA σ).toRingEquiv (primeCompl_map_σA t₀ σ)

theorem σR_algebraMap (g : A) : σR t₀ σ (algebraMap A (R t₀) g) = algebraMap A (R t₀) (σA σ g) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ _

theorem ringHom_ext_R {S : Type*} [CommRing S] {j k : R t₀ →+* S}
    (h : ∀ f : A, j (algebraMap A (R t₀) f) = k (algebraMap A (R t₀) f)) : j = k :=
  IsLocalization.ringHom_ext (P t₀).primeCompl (RingHom.ext h)

theorem galLift_algebraMap_R (r : R t₀) :
    galLift σ (algebraMap (R t₀) K0 r) = algebraMap (R t₀) K0 (σR t₀ σ r) := by
  have := ringHom_ext_R t₀ (j := (galLift σ : K0 →+* K0).comp (algebraMap (R t₀) K0))
    (k := (algebraMap (R t₀) K0).comp (σR t₀ σ).toRingHom) fun f => by
      simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe]
      rw [← IsScalarTower.algebraMap_apply, galLift_algebraMap, σR_algebraMap,
        ← IsScalarTower.algebraMap_apply, σA_apply]
  exact RingHom.congr_fun this r

theorem galLift_symm_algebraMap_R (r : R t₀) :
    (galLift σ).symm (algebraMap (R t₀) K0 r) = algebraMap (R t₀) K0 ((σR t₀ σ).symm r) := by
  rw [AlgEquiv.symm_apply_eq, galLift_algebraMap_R, RingEquiv.apply_symm_apply]

theorem eval_map_σ (f : A) : (f.map (σ : Qbar →+* Qbar)).eval (ι t₀) = σ (f.eval (ι t₀)) := by
  conv_lhs => rw [← σ_ι σ t₀]
  rw [eval_map, ← RingHom.coe_coe σ, eval₂_at_apply]

theorem resIso_residue_σR (r : R t₀) :
    resIso t₀ (IsLocalRing.residue (R t₀) (σR t₀ σ r)) = σ (resIso t₀ (IsLocalRing.residue (R t₀) r)) := by
  have := ringHom_ext_R t₀
    (j := ((resIso t₀).toRingHom.comp (IsLocalRing.residue (R t₀))).comp (σR t₀ σ).toRingHom)
    (k := ((σ : Qbar →+* Qbar).comp (resIso t₀).toRingHom).comp (IsLocalRing.residue (R t₀))) fun f => by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [σR_algebraMap, resIso_residue_algebraMap, resIso_residue_algebraMap, σA_apply, eval_map_σ]
  exact RingHom.congr_fun this r

abbrev v : Valuation K0 (WithZero (Multiplicative ℤ)) :=
  IsDedekindDomain.HeightOneSpectrum.valuation K0 (IsDiscreteValuationRing.maximalIdeal (R t₀))

theorem v_le_one_iff (z : K0) : v t₀ z ≤ 1 ↔ ∃ r : R t₀, algebraMap (R t₀) K0 r = z := by
  constructor
  · exact IsDiscreteValuationRing.exists_lift_of_le_one
  · rintro ⟨r, rfl⟩
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ r

theorem v_galLift_le_one_iff (z : K0) : v t₀ (galLift σ z) ≤ 1 ↔ v t₀ z ≤ 1 := by
  rw [v_le_one_iff, v_le_one_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(σR t₀ σ).symm r, ?_⟩
    rw [← galLift_symm_algebraMap_R, hr, AlgEquiv.symm_apply_apply]
  · rintro ⟨r, rfl⟩
    exact ⟨σR t₀ σ r, (galLift_algebraMap_R t₀ σ r).symm⟩

theorem reduceCoord_algebraMap (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] (r : S) :
    WeierstrassCurve.reduceCoord S (algebraMap S L r) = IsLocalRing.residue S r := by
  unfold WeierstrassCurve.reduceCoord
  have h : ∃ r' : S, algebraMap S L r' = algebraMap S L r := ⟨r, rfl⟩
  rw [dif_pos h]
  exact congrArg _ (IsFractionRing.injective S L h.choose_spec)

variable (W : WeierstrassCurve (Polynomial ℚ))

abbrev Wt₀ : WeierstrassCurve ℚ := W.map (Polynomial.evalRingHom t₀)

abbrev Et₀ : WeierstrassCurve Qbar := (W.map (Polynomial.evalRingHom t₀)).baseChange (AlgebraicClosure ℚ)

def WR : WeierstrassCurve (R t₀) := W.map (ψR t₀)

theorem WR_baseChange : (WR t₀ W).baseChange K0 = W⁄K0 := by
  unfold WR
  rw [WeierstrassCurve.baseChange, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext (algebraMap_R_K0_ψR t₀)

scoped instance Eη_isIntegral : (W⁄K0).IsIntegral (R t₀) := ⟨⟨WR t₀ W, (WR_baseChange t₀ W).symm⟩⟩

theorem Δ_Eη : (W⁄K0).Δ = algebraMap (R t₀) K0 (algebraMap A (R t₀) (W.Δ.map ι)) := by
  rw [Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, ← IsScalarTower.algebraMap_apply]
  rfl

theorem eval_Δ_map : (W.Δ.map ι).eval (ι t₀) = ι (W.Δ.eval t₀) := by
  rw [eval_map, eval₂_at_apply]

theorem valuation_Δ_eq_one_iff : v t₀ (W⁄K0).Δ = 1 ↔ W.Δ.eval t₀ ≠ 0 := by
  rw [Δ_Eη, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  show algebraMap A (R t₀) _ ∉ IsLocalRing.maximalIdeal (R t₀) ↔ _
  rw [algebraMap_mem_maximalIdeal_iff, eval_Δ_map, map_eq_zero_iff _ ι.injective]

theorem hasGoodReduction_of_eval_Δ_ne_zero (hΔ : W.Δ.eval t₀ ≠ 0) : (W⁄K0).HasGoodReduction (R t₀) := by
  have hv := (valuation_Δ_eq_one_iff t₀ W).mpr hΔ
  have hint : (W⁄K0).IsIntegral (R t₀) := inferInstance
  have hint1 : ((1 : WeierstrassCurve.VariableChange K0) • (W⁄K0)).IsIntegral (R t₀) := by rwa [one_smul]
  have h1 : (WeierstrassCurve.valuation_Δ_aux (R t₀) ((1 : WeierstrassCurve.VariableChange K0) • (W⁄K0))).1 = 1 := by
    rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral, one_smul]; exact hv
  have hmin : (W⁄K0).IsMinimal (R t₀) := by
    refine WeierstrassCurve.IsMinimal.mk (And.intro hint1 fun C hC hle => ?_)
    change (WeierstrassCurve.valuation_Δ_aux (R t₀) (C • (W⁄K0))).1 ≤
      (WeierstrassCurve.valuation_Δ_aux (R t₀) ((1 : WeierstrassCurve.VariableChange K0) • (W⁄K0))).1
    rw [h1]
    exact (WeierstrassCurve.valuation_Δ_aux (R t₀) (C • (W⁄K0))).2
  exact WeierstrassCurve.HasGoodReduction.mk (toIsMinimal := hmin) (goodReduction := hv)

end CAlpha
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_specializationHom.CAlpha"

namespace CAlpha

variable (t₀ : ℚ) (σ : Qbar ≃ₐ[ℚ] Qbar) (W : WeierstrassCurve (Polynomial ℚ))

section WithGoodReduction

variable [hΔ : Fact (W.Δ.eval t₀ ≠ 0)]

scoped instance Eη_hasGoodReduction : (W⁄K0).HasGoodReduction (R t₀) :=
  hasGoodReduction_of_eval_Δ_ne_zero t₀ W hΔ.out

def Ered : WeierstrassCurve (IsLocalRing.ResidueField (R t₀)) := (W⁄K0).reduction (R t₀)

omit hΔ in
theorem integralModel_eq : WeierstrassCurve.integralModel (R t₀) (W⁄K0) = WR t₀ W :=
  WeierstrassCurve.map_injective (IsFractionRing.injective (R t₀) K0) <| by
    change (WeierstrassCurve.integralModel (R t₀) (W⁄K0)).baseChange K0 = (WR t₀ W).baseChange K0
    rw [WeierstrassCurve.baseChange_integralModel_eq, WR_baseChange]

theorem Ered_eq : Ered t₀ W = W.map ((IsLocalRing.residue (R t₀)).comp (ψR t₀)) := by
  unfold Ered
  rw [WeierstrassCurve.reduction, integralModel_eq, WR, WeierstrassCurve.map_map]

theorem resIso_comp_residue_comp_ψR :
    ((resIso t₀).toRingHom.comp ((IsLocalRing.residue (R t₀)).comp (ψR t₀))) = ι.comp (Polynomial.evalRingHom t₀) := by
  refine Polynomial.ringHom_ext (fun q => ?_) ?_
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Polynomial.coe_mapRingHom,
      Polynomial.map_C, Polynomial.coe_evalRingHom, eval_C]
    exact resIso_residue_C t₀ _
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Polynomial.coe_mapRingHom,
      Polynomial.map_X, Polynomial.coe_evalRingHom, eval_X]
    exact resIso_residue_X t₀

theorem Ered_map_resIso : (Ered t₀ W).map (resIso t₀).toRingHom = Et₀ t₀ W := by
  rw [Ered_eq, WeierstrassCurve.map_map, resIso_comp_residue_comp_ψR, ← WeierstrassCurve.map_map]
  rfl

def redHom : (W⁄K0).toAffine.Point →+ ((Ered t₀ W)⁄(IsLocalRing.ResidueField (R t₀))).Point where
  toFun P := WeierstrassCurve.reducePoint_alt (R t₀) (W⁄K0) P
  map_zero' := rfl
  map_add' := WeierstrassCurve.reducePoint_add (R t₀) (W⁄K0)

theorem redHom_apply (Pt : (W⁄K0).toAffine.Point) : redHom t₀ W Pt = WeierstrassCurve.reducePoint_alt (R t₀) (W⁄K0) Pt := rfl

@[reducible] def algebraResQbar : Algebra (IsLocalRing.ResidueField (R t₀)) Qbar := (resIso t₀).toRingHom.toAlgebra

attribute [local instance] algebraResQbar

theorem algebraMap_res_Qbar (a : IsLocalRing.ResidueField (R t₀)) :
    algebraMap (IsLocalRing.ResidueField (R t₀)) Qbar a = resIso t₀ a := rfl

def pointCongrFun {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point → W₂.toAffine.Point
  | .zero => .zero
  | .some x y hp => .some x y (h ▸ hp)

theorem pointCongrFun_refl {F : Type*} [Field F] {W₁ : WeierstrassCurve F} (P : W₁.toAffine.Point) :
    pointCongrFun (rfl : W₁ = W₁) P = P := by
  cases P <;> rfl

def pointCongr {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point where
  toFun := pointCongrFun h
  invFun := pointCongrFun h.symm
  left_inv P := by subst h; cases P <;> rfl
  right_inv P := by subst h; cases P <;> rfl
  map_add' P Q := by
    subst h
    show pointCongrFun rfl (P + Q) = pointCongrFun rfl P + pointCongrFun rfl Q
    rw [pointCongrFun_refl, pointCongrFun_refl, pointCongrFun_refl]

theorem pointCongr_some {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂)
    {x y : F} (hp : W₁.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hp) = .some x y (h ▸ hp) := rfl

theorem baseChange_Ered_Qbar : (Ered t₀ W).baseChange Qbar = Et₀ t₀ W := Ered_map_resIso t₀ W

def sp : (W⁄K0).toAffine.Point →+ (Et₀ t₀ W).toAffine.Point :=
  (pointCongr (baseChange_Ered_Qbar t₀ W)).toAddMonoidHom.comp <|
    (WeierstrassCurve.Affine.Point.map (W' := Ered t₀ W)
        (Algebra.ofId (IsLocalRing.ResidueField (R t₀)) Qbar)).comp (redHom t₀ W)

def redHomPt (a b : IsLocalRing.ResidueField (R t₀)) (hab : ((W⁄K0).reduction (R t₀)).toAffine.Nonsingular a b) :
    ((Ered t₀ W)⁄(IsLocalRing.ResidueField (R t₀))).Point :=
  WeierstrassCurve.Affine.Point.some a b hab

theorem redHom_some_eq {x y : K0} {h : (W⁄K0).toAffine.Nonsingular x y} {a b : IsLocalRing.ResidueField (R t₀)}
    {hab : ((W⁄K0).reduction (R t₀)).toAffine.Nonsingular a b}
    (e : WeierstrassCurve.reducePoint_alt (R t₀) (W⁄K0) (.some x y h) = .some a b hab) :
    redHom t₀ W (.some x y h) = redHomPt t₀ W a b hab := e

theorem sp_apply (Pt : (W⁄K0).toAffine.Point) :
    sp t₀ W Pt = pointCongr (baseChange_Ered_Qbar t₀ W)
      (WeierstrassCurve.Affine.Point.map (W' := Ered t₀ W) (Algebra.ofId (IsLocalRing.ResidueField (R t₀)) Qbar)
        (redHom t₀ W Pt)) := rfl

theorem map_ofId_some (a b : IsLocalRing.ResidueField (R t₀))
    (hab : ((W⁄K0).reduction (R t₀)).toAffine.Nonsingular a b) :
    WeierstrassCurve.Affine.Point.map (W' := Ered t₀ W) (Algebra.ofId (IsLocalRing.ResidueField (R t₀)) Qbar)
        (redHomPt t₀ W a b hab) =
      .some (resIso t₀ a) (resIso t₀ b)
        (((Ered t₀ W).toAffine.baseChange_nonsingular (f := Algebra.ofId (IsLocalRing.ResidueField (R t₀)) Qbar)
          (resIso t₀).injective a b).mpr hab) := rfl

theorem sp_eq_zero_of_red {Pt : (W⁄K0).toAffine.Point}
    (e : redHom t₀ W Pt = 0) : sp t₀ W Pt = 0 := by
  rw [sp_apply, e, _root_.map_zero, _root_.map_zero]

theorem sp_some_of_lift {x y : K0} (h : (W⁄K0).toAffine.Nonsingular x y) (r s : R t₀)
    (hr : algebraMap (R t₀) K0 r = x) (hs : algebraMap (R t₀) K0 s = y) :
    sp t₀ W (.some x y h) =
      pt (Et₀ t₀ W) (resIso t₀ (IsLocalRing.residue (R t₀) r)) (resIso t₀ (IsLocalRing.residue (R t₀) s)) := by
  subst hr hs
  have hx : v t₀ (algebraMap (R t₀) K0 r) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ r
  have hy : v t₀ (algebraMap (R t₀) K0 s) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ s
  obtain ⟨h₁, e₁⟩ := WeierstrassCurve.reducePoint_some (R t₀) (W⁄K0) h hx hy
  rw [sp_apply, redHom_some_eq t₀ W e₁, map_ofId_some, pointCongr_some, ← pt_eq_some,
    reduceCoord_algebraMap, reduceCoord_algebraMap]

theorem sp_zero : sp t₀ W 0 = 0 := map_zero _

omit hΔ in

theorem smul_pt (X Y : Qbar) : σ • pt (Et₀ t₀ W) X Y = pt (Et₀ t₀ W) (σ X) (σ Y) := by
  by_cases hns : (Et₀ t₀ W).toAffine.Nonsingular X Y
  · have hns' : (Et₀ t₀ W).toAffine.Nonsingular (σ X) (σ Y) :=
      ((Wt₀ t₀ W).toAffine.baseChange_nonsingular (f := σ.toAlgHom) σ.toAlgHom.injective X Y).mpr hns
    rw [pt_eq_some hns, pt_eq_some hns', WeierstrassCurve.Affine.Point.algEquiv_smul_def,
      WeierstrassCurve.Affine.Point.map_some]
    rfl
  · have hns' : ¬ (Et₀ t₀ W).toAffine.Nonsingular (σ X) (σ Y) := fun h' =>
      hns (((Wt₀ t₀ W).toAffine.baseChange_nonsingular (f := σ.toAlgHom) σ.toAlgHom.injective X Y).mp h')
    rw [pt_eq_zero hns, pt_eq_zero hns']
    rfl

theorem sp_galois (Pt : (W⁄K0).toAffine.Point) : sp t₀ W (galLift σ • Pt) = σ • sp t₀ W Pt := by
  rcases Pt with _ | ⟨x, y, h⟩
  · show sp t₀ W 0 = σ • sp t₀ W 0
    rw [sp_zero]
    rfl
  · rw [WeierstrassCurve.Affine.Point.algEquiv_smul_def, WeierstrassCurve.Affine.Point.map_some]
    by_cases hx : v t₀ x ≤ 1
    ·
      have hy : v t₀ y ≤ 1 := by
        by_contra hy
        have e0 : WeierstrassCurve.reducePoint_alt (R t₀) (W⁄K0) (.some x y h) = .zero := by
          simp only [WeierstrassCurve.reducePoint_alt, hy, and_false, dite_false]
        exact ((WeierstrassCurve.reducePoint_some_eq_zero_iff (R t₀) (W⁄K0) h).mp e0) hx
      obtain ⟨r, hr⟩ := (v_le_one_iff t₀ x).mp hx
      obtain ⟨s, hs⟩ := (v_le_one_iff t₀ y).mp hy
      have hr' : algebraMap (R t₀) K0 (σR t₀ σ r) = galLift σ x := by rw [← galLift_algebraMap_R, hr]
      have hs' : algebraMap (R t₀) K0 (σR t₀ σ s) = galLift σ y := by rw [← galLift_algebraMap_R, hs]
      change sp t₀ W (.some (galLift σ x) (galLift σ y) _) = σ • sp t₀ W (.some x y h)
      rw [sp_some_of_lift t₀ W _ (σR t₀ σ r) (σR t₀ σ s) hr' hs', sp_some_of_lift t₀ W h r s hr hs,
        smul_pt, resIso_residue_σR, resIso_residue_σR]
    ·
      have hx' : ¬ v t₀ (galLift σ x) ≤ 1 := by rwa [v_galLift_le_one_iff]
      have e0 : redHom t₀ W (.some x y h) = 0 :=
        (WeierstrassCurve.reducePoint_some_eq_zero_iff (R t₀) (W⁄K0) h).mpr hx
      have hns : (W⁄K0).toAffine.Nonsingular (galLift σ x) (galLift σ y) :=
        ((W.toAffine).baseChange_nonsingular (f := (galLift σ).toAlgHom) (galLift σ).toAlgHom.injective x y).mpr h
      have e0' : redHom t₀ W (.some (galLift σ x) (galLift σ y) hns) = 0 :=
        (WeierstrassCurve.reducePoint_some_eq_zero_iff (R t₀) (W⁄K0) hns).mpr hx'
      change sp t₀ W (.some (galLift σ x) (galLift σ y) _) = σ • sp t₀ W (.some x y h)
      rw [sp_eq_zero_of_red t₀ W e0, sp_eq_zero_of_red t₀ W e0']
      rfl

theorem sp_torsion_injective {n : ℕ} (hn : n ≠ 0) (Pt : (W⁄K0).toAffine.Point) (hP : n • Pt = 0)
    (h0 : sp t₀ W Pt = 0) : Pt = 0 := by
  have hred : redHom t₀ W Pt = 0 := by
    rw [sp_apply] at h0
    have h1 := (pointCongr (baseChange_Ered_Qbar t₀ W)).injective (h0.trans (_root_.map_zero _).symm)
    exact WeierstrassCurve.Affine.Point.map_injective (W' := Ered t₀ W) _ (h1.trans (_root_.map_zero _).symm)
  have hn' : (n : IsLocalRing.ResidueField (R t₀)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  exact WeierstrassCurve.eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero (R t₀) (W⁄K0) hn' Pt hP hred

theorem sp_some_algebraMap (x y : A)
    (h : (W⁄K0).toAffine.Nonsingular (algebraMap A K0 x) (algebraMap A K0 y)) :
    sp t₀ W (.some (algebraMap A K0 x) (algebraMap A K0 y) h) =
      pt (Et₀ t₀ W) (x.eval (ι t₀)) (y.eval (ι t₀)) := by
  rw [sp_some_of_lift t₀ W h (algebraMap A (R t₀) x) (algebraMap A (R t₀) y)
      (IsScalarTower.algebraMap_apply A (R t₀) K0 x).symm (IsScalarTower.algebraMap_apply A (R t₀) K0 y).symm,
    resIso_residue_algebraMap, resIso_residue_algebraMap]

end WithGoodReduction
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_specializationHom.CAlpha"

end CAlpha
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_specializationHom.CAlpha"

theorem solution (W : WeierstrassCurve (Polynomial ℚ)) (t₀ : ℚ) (hΔ : W.Δ.eval t₀ ≠ 0) : ∃ s : (W⁄(FractionRing (Polynomial (AlgebraicClosure ℚ)))).Point →+ ((W.map (Polynomial.evalRingHom t₀))⁄(AlgebraicClosure ℚ)).Point, (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : (W⁄(FractionRing (Polynomial (AlgebraicClosure ℚ)))).Point), s (galLift σ • P) = σ • s P) ∧ (∀ (n : ℕ), n ≠ 0 → ∀ P : (W⁄(FractionRing (Polynomial (AlgebraicClosure ℚ)))).Point, n • P = 0 → s P = 0 → P = 0) ∧ (∀ (x y : Polynomial (AlgebraicClosure ℚ)) (h : (W⁄(FractionRing (Polynomial (AlgebraicClosure ℚ)))).toAffine.Nonsingular (algebraMap (Polynomial (AlgebraicClosure ℚ)) (FractionRing (Polynomial (AlgebraicClosure ℚ))) x) (algebraMap (Polynomial (AlgebraicClosure ℚ)) (FractionRing (Polynomial (AlgebraicClosure ℚ))) y)), s (Point.some (algebraMap (Polynomial (AlgebraicClosure ℚ)) (FractionRing (Polynomial (AlgebraicClosure ℚ))) x) (algebraMap (Polynomial (AlgebraicClosure ℚ)) (FractionRing (Polynomial (AlgebraicClosure ℚ))) y) h) = pt ((W.map (Polynomial.evalRingHom t₀)).baseChange (AlgebraicClosure ℚ)) (x.eval (algebraMap ℚ (AlgebraicClosure ℚ) t₀)) (y.eval (algebraMap ℚ (AlgebraicClosure ℚ) t₀))) := by
  haveI : Fact (W.Δ.eval t₀ ≠ 0) := ⟨hΔ⟩
  exact ⟨CAlpha.sp t₀ W, fun σ P => CAlpha.sp_galois t₀ σ W P,
    fun n hn P hP h0 => CAlpha.sp_torsion_injective t₀ W hn P hP h0,
    fun x y h => CAlpha.sp_some_algebraMap t₀ W x y h⟩

#print axioms solution

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_specializationHom.CAlpha"

end S_WeierstrassCurve_exists_specializationHom
end P2MW
export P2MW.S_WeierstrassCurve_exists_specializationHom (solution)

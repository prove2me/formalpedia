-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel.isUnit_indepElt_of_isSectionThrough
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5ae8556a-ad81-5f63-b533-fcfc56caa3b0

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_map_eq_smul_one_of_zlinComb_eq_zsmulSection
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_isUnit_indepElt_of_isSectionThrough
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped Classical

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ModularCurve.LevelRelabelling

noncomputable section
namespace C2Aux

variable {T : Type} [Field T]

local notation "tT" => Spec.map (CommRingCat.ofHom (algebraMap T T))

lemma tT_eq : (tT : base (T := T) ⟶ base (T := T)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

lemma hψ : 𝟙 (base (T := T)) ≫ 𝟙 (base (T := T)) = tT := by
  rw [Category.id_comp, tT_eq]

variable (W : WeierstrassCurve.Projective T)

def τ (S : Section W) : NeronModelInfra.SchemeHomOver tT (projModelStrCR W) :=
  schemeHomOverComp (𝟙 _) hψ S

lemma τ_val (S : Section W) : (τ W S).1 = S.1 := by
  show 𝟙 _ ≫ S.1 = S.1
  exact Category.id_comp _

lemma τ_injective : Function.Injective (τ W) := by
  intro S₁ S₂ h
  apply Subtype.ext
  rw [← τ_val W S₁, ← τ_val W S₂, h]

variable (G : RelativeGroupLaw T (projModelStrCR W))

lemma τ_mul (X Y : Section W) : τ W (G.mul (𝟙 _) X Y) = G.mul tT (τ W X) (τ W Y) :=
  G.mul_natural _ _ _ hψ X Y

lemma τ_nsmul (n : ℕ) (X : Section W) : τ W (G.nsmul (𝟙 _) n X) = G.nsmul tT n (τ W X) :=
  G.nsmul_natural _ _ _ hψ n X

lemma τ_one : τ W (G.one (𝟙 _)) = G.one tT :=
  G.one_natural _ _ _ hψ

lemma bc_eq : W.baseChange T = W := by
  show W.map (algebraMap T T) = W
  rw [Algebra.algebraMap_self]
  exact W.map_id

def ptCast {W₁ W₂ : WeierstrassCurve T} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

lemma ptCast_some {W₁ W₂ : WeierstrassCurve T} (e : W₁ = W₂) (x y : T) (h : W₁.toAffine.Nonsingular x y) :
    ∃ h' : W₂.toAffine.Nonsingular x y, ptCast e (.some x y h) = .some x y h' := by
  subst e; exact ⟨h, rfl⟩

variable (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
    NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W) ≃
      (W.baseChange F).toAffine.Point)

def Φ (S : Section W) : W.toAffine.Point := ptCast (bc_eq W) (ev T (τ W S))

lemma Φ_injective : Function.Injective (Φ W ev) := fun _ _ h =>
  τ_injective W ((ev T).injective ((ptCast (bc_eq W)).injective h))

lemma Φ_mul (hev : IsPointsEval W G ev) (X Y : Section W) :
    Φ W ev (G.mul (𝟙 _) X Y) = Φ W ev X + Φ W ev Y := by
  unfold Φ
  rw [τ_mul, hev.1, map_add]

lemma Φ_one (hG1 : (G.one (𝟙 _)).1 = (kwZeroSect T W).1)
    (hev0 : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
      ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
        by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0) :
    Φ W ev (G.one (𝟙 _)) = 0 := by
  unfold Φ
  have h1 : G.one tT = ⟨tT ≫ (kwZeroSect T W).1,
      by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ := by
    rw [← τ_one W G]
    apply Subtype.ext
    show 𝟙 _ ≫ (G.one (𝟙 _)).1 = tT ≫ (kwZeroSect T W).1
    rw [hG1, tT_eq]
  rw [τ_one, h1, hev0 T, map_zero]

lemma Φ_nsmul (hev : IsPointsEval W G ev) (hG1 : (G.one (𝟙 _)).1 = (kwZeroSect T W).1)
    (hev0 : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
      ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
        by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0)
    (n : ℕ) (X : Section W) :
    Φ W ev (G.nsmul (𝟙 _) n X) = n • Φ W ev X := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, Φ_one W G ev hG1 hev0, zero_nsmul]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, Φ_mul W G ev hev, ih, add_nsmul, one_nsmul]

lemma Φ_through
    (hevc : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F]
      (P : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W))
      (χ : ZChartRing W →+* F),
      P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W →
      ∃ hxy : (W.baseChange F).toAffine.Nonsingular (χ (xOverZ W)) (χ (yOverZ W)),
        ev F P = WeierstrassCurve.Affine.Point.some _ _ hxy)
    (S : Section W) (χ : ZChartRing W →+* T) (hS : IsZChartSection S χ) :
    Φ W ev S = toPoint W (affX χ) (affY χ) := by
  obtain ⟨hxy, h⟩ := hevc T (τ W S) χ (by rw [τ_val]; exact hS)
  unfold Φ
  rw [h]
  obtain ⟨h', e'⟩ := ptCast_some (bc_eq W) (χ (xOverZ W)) (χ (yOverZ W)) hxy
  rw [e']
  show _ = toPoint W (χ (xOverZ W)) (χ (yOverZ W))
  rw [toPoint, dif_pos h']

lemma Φ_through'
    (hevc : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F]
      (P : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W))
      (χ : ZChartRing W →+* F),
      P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W →
      ∃ hxy : (W.baseChange F).toAffine.Nonsingular (χ (xOverZ W)) (χ (yOverZ W)),
        ev F P = WeierstrassCurve.Affine.Point.some _ _ hxy)
    (S : Section W) (χ : ZChartRing W →+* T) (hS : IsZChartSection S χ) :
    ∃ h' : W.toAffine.Nonsingular (affX χ) (affY χ), Φ W ev S = WeierstrassCurve.Affine.Point.some _ _ h' := by
  obtain ⟨hxy, h⟩ := hevc T (τ W S) χ (by rw [τ_val]; exact hS)
  obtain ⟨h', e'⟩ := ptCast_some (bc_eq W) (χ (xOverZ W)) (χ (yOverZ W)) hxy
  exact ⟨h', by unfold Φ; rw [h, e']; rfl⟩

lemma Φ_inv (hev : IsPointsEval W G ev) (hG1 : (G.one (𝟙 _)).1 = (kwZeroSect T W).1)
    (hev0 : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
      ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
        by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0)
    (X : Section W) : Φ W ev (G.inv (𝟙 _) X) = - Φ W ev X := by
  have h := Φ_mul W G ev hev (G.inv (𝟙 _) X) X
  rw [G.inv_mul_cancel, Φ_one W G ev hG1 hev0] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

lemma Φ_zsmulSection (hev : IsPointsEval W G ev) (hG1 : (G.one (𝟙 _)).1 = (kwZeroSect T W).1)
    (hev0 : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
      ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
        by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0)
    (z : ℤ) (X : Section W) :
    Φ W ev (ModularCurve.LevelRelabelling.zsmulSection G z X) = z • Φ W ev X := by
  cases z with
  | ofNat k =>
      rw [show ModularCurve.LevelRelabelling.zsmulSection G (Int.ofNat k) X = G.nsmul _ k X from rfl,
        Φ_nsmul W G ev hev hG1 hev0, Int.ofNat_eq_coe, natCast_zsmul]
  | negSucc k =>
      rw [show ModularCurve.LevelRelabelling.zsmulSection G (Int.negSucc k) X = G.inv _ (G.nsmul _ (k + 1) X) from rfl,
        Φ_inv W G ev hev hG1 hev0, Φ_nsmul W G ev hev hG1 hev0, negSucc_zsmul]

lemma Φ_zlinComb (hev : IsPointsEval W G ev) (hG1 : (G.one (𝟙 _)).1 = (kwZeroSect T W).1)
    (hev0 : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
      ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
        by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0)
    (P Q : Section W) (a b : ℤ) :
    Φ W ev (ModularCurve.LevelRelabelling.zlinComb G P Q a b) = a • Φ W ev P + b • Φ W ev Q := by
  show Φ W ev (G.mul _ _ _) = _
  rw [Φ_mul W G ev hev, Φ_zsmulSection W G ev hev hG1 hev0, Φ_zsmulSection W G ev hev hG1 hev0]

end C2Aux

namespace C2Tors

theorem nsmul_val {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)) (n : ℕ)
    (P : NeronModelInfra.SchemeHomOver t (projModelStrCR W)) :
    (G.nsmul t n P).1 = P.1 ≫ G.schemeNsmul n := by
  have h := G.nsmul_natural (projModelStrCR W) t P.1 P.2 n RelativeGroupLaw.idPoint
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := projModelStrCR W)) = P :=
    Subtype.ext (Category.comp_id _)
  rw [hP] at h
  rw [← h]
  rfl

theorem nsmul_eq_one_of_isDrinfeldBasis {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) {q : ℕ} (hq : 2 ≤ q) {P Q : Section W}
    (h : IsDrinfeldBasis G q P Q) :
    G.nsmul (𝟙 _) q P = G.one (𝟙 _) ∧ G.nsmul (𝟙 _) q Q = G.one (𝟙 _) := by
  have h' := (isDrinfeldBasis_iff_isDrinfeldBasisOver_id G q P Q).mp h
  obtain ⟨⟨pP, hpP⟩, ⟨pQ, hpQ⟩⟩ := RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq G hq h'
  have h1 : pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ projModelStrCR W =
      pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1 := by
    calc pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ projModelStrCR W
        = pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ (G.schemeNsmul q ≫ projModelStrCR W) := by
          rw [G.schemeNsmul_over]
      _ = (pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ G.schemeNsmul q) ≫ projModelStrCR W :=
          (Category.assoc _ _ _).symm
      _ = (pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ (G.one (𝟙 _)).1) ≫ projModelStrCR W := by
          rw [pullback.condition]
      _ = pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1 := by
          rw [Category.assoc, (G.one (𝟙 _)).2, Category.comp_id]
  have key : ∀ (S : Section W) (p : Spec (CommRingCat.of T) ⟶ G.schemeKer q),
      p ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = S.1 → G.nsmul (𝟙 _) q S = G.one (𝟙 _) := by
    intro S p hp
    have hsnd : p ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1 = 𝟙 _ := by
      rw [← h1, ← Category.assoc, hp, S.2]
    apply Subtype.ext
    rw [nsmul_val, ← hp, Category.assoc, pullback.condition, ← Category.assoc, hsnd, Category.id_comp]
  exact ⟨key P pP hpP, key Q pQ hpQ⟩

end C2Tors

theorem C2_indepElt_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (W : WeierstrassCurve A) (p : ℕ)
    (x₀ x : A) : f (ModularCurve.indepElt W p x₀ x) = ModularCurve.indepElt (W.map f) p (f x₀) (f x) := by
  simp only [ModularCurve.indepElt, map_prod, map_sub, map_mul, WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_Φ,
    Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem C2_isUnit_of_forall_maximal {R₀ T : Type*} [CommRing R₀] [CommRing T] [Algebra R₀ T] (a : T)
    (h : ∀ (𝔪 : Ideal T) [𝔪.IsMaximal], Ideal.Quotient.mkₐ R₀ 𝔪 a ≠ 0) : IsUnit a := by
  by_contra hu
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (mt Ideal.span_singleton_eq_top.mp hu)
  haveI := h𝔪
  exact h 𝔪 (Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_span_singleton_self a)))

open C2Aux in
set_option maxHeartbeats 3200000 in

theorem C2_core {A₀ : Type} [CommRing A₀] (𝒢 : GroupLaws A₀) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) {K : Type} [CommRing K] [Algebra A₀ K] (hK : IsField K) (hqK : (q : K) ≠ 0)
    (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ) (P Q : Section W)
    (hPQ : IsDrinfeldBasis (𝒢 K W hΔ) q P Q) (xP yP xQ yQ : K)
    (hP : IsSectionThrough P xP yP) (hQ : IsSectionThrough Q xQ yQ) :
    ModularCurve.indepElt W q xP xQ ≠ 0 ∧ ModularCurve.indepElt W q xQ xP ≠ 0 := by
  classical
  letI : Field K := hK.toField
  haveI : WeierstrassCurve.IsElliptic W := ⟨hΔ⟩
  have hG1 : ((𝒢 K W hΔ).one (𝟙 _)).1 = (kwZeroSect K W).1 :=
    (RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢 K W hΔ)).mp (h𝒢O K W hΔ)
  obtain ⟨ev, hev, hev0, hevc⟩ :=
    exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain W (𝒢 K W hΔ) hG1
  obtain ⟨hqP, hqQ⟩ := C2Tors.nsmul_eq_one_of_isDrinfeldBasis (𝒢 K W hΔ) (Nat.Prime.two_le Fact.out) hPQ
  obtain ⟨χ, hχ, rfl, rfl⟩ := hP
  obtain ⟨χ', hχ', rfl, rfl⟩ := hQ
  obtain ⟨nP, eP⟩ := Φ_through' W ev hevc P χ hχ
  obtain ⟨nQ, eQ⟩ := Φ_through' W ev hevc Q χ' hχ'
  have tP : q • WeierstrassCurve.Affine.Point.some _ _ nP = 0 := by
    rw [← eP, ← Φ_nsmul W _ ev hev hG1 hev0, hqP, Φ_one W _ ev hG1 hev0]
  have tQ : q • WeierstrassCurve.Affine.Point.some _ _ nQ = 0 := by
    rw [← eQ, ← Φ_nsmul W _ ev hev hG1 hev0, hqQ, Φ_one W _ ev hG1 hev0]
  have hzlin := Φ_zlinComb W (𝒢 K W hΔ) ev hev hG1 hev0 P Q
  have hzs := Φ_zsmulSection W (𝒢 K W hΔ) ev hev hG1 hev0
  constructor
  · intro h0
    have hmem := (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hq2 nP nQ tP).mp h0
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    rw [← eP, ← eQ] at hn
    have g00 : (!![1, n; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := rfl
    have g10 : (!![1, n; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := rfl
    have g01 : (!![1, n; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = n := rfl
    have g11 : (!![1, n; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := rfl
    have L1 : Φ W ev (ModularCurve.LevelRelabelling.zlinComb (𝒢 K W hΔ) P Q
        ((!![1, n; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((!![1, n; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) =
        Φ W ev P := by
      rw [hzlin, g00, g10, one_smul, zero_smul, add_zero]
    have L2 : Φ W ev (ModularCurve.LevelRelabelling.zlinComb (𝒢 K W hΔ) P Q
        ((!![1, n; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) 0 1) ((!![1, n; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) =
        Φ W ev Q := by
      rw [hzlin, g01, g11, zero_smul, add_zero]; exact hn
    have R1 : Φ W ev (ModularCurve.LevelRelabelling.zsmulSection (𝒢 K W hΔ) 1 P) = Φ W ev P := by
      rw [hzs, one_smul]
    have R2 : Φ W ev (ModularCurve.LevelRelabelling.zsmulSection (𝒢 K W hΔ) 1 Q) = Φ W ev Q := by
      rw [hzs, one_smul]
    have key := IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection W hΔ (𝒢 K W hΔ) ev hev q hqK P Q hPQ
      !![1, n; 0, 0] 1 (Or.inl rfl) (Φ_injective W ev (L1.trans R1.symm)) (Φ_injective W ev (L2.trans R2.symm))
    have h11 := congr_fun (congr_fun key 1) 1
    rw [Matrix.map_apply, g11] at h11
    simp at h11
  · intro h0
    have hmem := (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hq2 nQ nP tQ).mp h0
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    rw [← eP, ← eQ] at hn
    have g00 : (!![0, 0; n, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0 := rfl
    have g10 : (!![0, 0; n, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = n := rfl
    have g01 : (!![0, 0; n, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := rfl
    have g11 : (!![0, 0; n, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := rfl
    have L1 : Φ W ev (ModularCurve.LevelRelabelling.zlinComb (𝒢 K W hΔ) P Q
        ((!![0, 0; n, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((!![0, 0; n, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) =
        Φ W ev P := by
      rw [hzlin, g00, g10, zero_smul, zero_add]; exact hn
    have L2 : Φ W ev (ModularCurve.LevelRelabelling.zlinComb (𝒢 K W hΔ) P Q
        ((!![0, 0; n, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1) ((!![0, 0; n, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) =
        Φ W ev Q := by
      rw [hzlin, g01, g11, zero_smul, zero_add, one_smul]
    have R1 : Φ W ev (ModularCurve.LevelRelabelling.zsmulSection (𝒢 K W hΔ) 1 P) = Φ W ev P := by
      rw [hzs, one_smul]
    have R2 : Φ W ev (ModularCurve.LevelRelabelling.zsmulSection (𝒢 K W hΔ) 1 Q) = Φ W ev Q := by
      rw [hzs, one_smul]
    have key := IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection W hΔ (𝒢 K W hΔ) ev hev q hqK P Q hPQ
      !![0, 0; n, 1] 1 (Or.inl rfl) (Φ_injective W ev (L1.trans R1.symm)) (Φ_injective W ev (L2.trans R2.symm))
    have h00 := congr_fun (congr_fun key 0) 0
    rw [Matrix.map_apply, g00] at h00
    simp at h00

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T : Type} [CommRing T] [Algebra A₀ T] (E : WeierstrassCurve T) (hq : IsUnit ((q : ℕ) : T))
    (x : RawDrinfeldPair T) (hx : RawDrinfeldPair.IsLevel 𝒢 q E x)
    (xP yP xQ yQ : T) (hP : IsSectionThrough x.P xP yP) (hQ : IsSectionThrough x.Q xQ yQ) :
    IsUnit (ModularCurve.indepElt E q xP xQ) ∧ IsUnit (ModularCurve.indepElt E q xQ xP) := by
  classical
  obtain ⟨hcE, hΔ, hDB⟩ := hx
  subst hcE
  have main : ∀ (𝔪 : Ideal T) [𝔪.IsMaximal],
      Ideal.Quotient.mkₐ A₀ 𝔪 (ModularCurve.indepElt x.curve q xP xQ) ≠ 0 ∧
        Ideal.Quotient.mkₐ A₀ 𝔪 (ModularCurve.indepElt x.curve q xQ xP) ≠ 0 := by
    intro 𝔪 _
    set f : T →ₐ[A₀] (T ⧸ 𝔪) := Ideal.Quotient.mkₐ A₀ 𝔪 with hf
    have hqκ : ((q : ℕ) : T ⧸ 𝔪) ≠ 0 := by
      have h := hq.map f
      rw [map_natCast] at h
      exact h.ne_zero
    obtain ⟨φ, hφ, hcoef⟩ := exists_isCoefficientHom x.curve f.toRingHom
    obtain ⟨hP', hQ'⟩ := isSectionThrough_map_of_isSectionTransport A₀ 𝒢 q 𝒯 h𝒯 f x ⟨φ, hφ, hcoef⟩
      ⟨xP, yP, xQ, yQ⟩ hP hQ
    obtain ⟨hc', hΔ', hDB'⟩ := 𝒯.isLevel_map f x.curve x ⟨rfl, hΔ, hDB⟩
    have hK : IsField (T ⧸ 𝔪) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔪).mp ‹_›
    have hcore := C2_core 𝒢 h𝒢O q hq2 hK hqκ (𝒯.map f x).curve hΔ' _ _ hDB' _ _ _ _ hP' hQ'
    rw [hc'] at hcore
    change f.toRingHom (ModularCurve.indepElt x.curve q xP xQ) ≠ 0 ∧ f.toRingHom (ModularCurve.indepElt x.curve q xQ xP) ≠ 0
    rw [C2_indepElt_map, C2_indepElt_map]
    exact hcore
  exact ⟨C2_isUnit_of_forall_maximal (R₀ := A₀) _ fun 𝔪 _ => (main 𝔪).1,
    C2_isUnit_of_forall_maximal (R₀ := A₀) _ fun 𝔪 _ => (main 𝔪).2⟩

end
end S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_isUnit_indepElt_of_isSectionThrough
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_isUnit_indepElt_of_isSectionThrough (solution)

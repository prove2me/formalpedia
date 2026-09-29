-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4da64c5c-a67b-5961-b819-4c81b8a65688

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_WeierstrassProjModel_schemeNsmul_flat_of_isPointsEval_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_mul_comm_of_isPointsEval
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassCurve_Affine_Point_card_le_sq_of_forall_nsmul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

namespace P2MKcDrin

universe u

theorem ker_eq_vanishingIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range f), isClosed_closure⟩ := by
  have hsupp : f.ker.support = ⟨closure (Set.range f), isClosed_closure⟩ :=
    TopologicalSpace.Closeds.ext (f.support_ker)
  rw [← hsupp, Scheme.IdealSheafData.vanishingIdeal_support]
  refine le_antisymm (Scheme.IdealSheafData.le_radical _) ?_
  rw [Scheme.IdealSheafData.le_def]
  intro U
  rw [Scheme.IdealSheafData.radical_ideal, f.ker_apply U]
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsReduced.eq_zero _ ⟨n, hn⟩

theorem ker_eq_vanishingIdeal_range {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    [IsReduced X] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal ⟨Set.range f, f.isClosedEmbedding.isClosed_range⟩ := by
  rw [ker_eq_vanishingIdeal]
  congr 1
  exact TopologicalSpace.Closeds.ext f.isClosedEmbedding.isClosed_range.closure_eq

theorem section_eq_of_apply_eq {K : Type u} [Field K] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of K)) (g₁ g₂ : Spec (CommRingCat.of K) ⟶ Y)
    (h₁ : g₁ ≫ p = 𝟙 _) (h₂ : g₂ ≫ p = 𝟙 _) (s : Spec (CommRingCat.of K))
    (h : g₁ s = g₂ s) : g₁ = g₂ := by
  obtain ⟨⟨y₁, φ₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective g₁
  obtain ⟨⟨y₂, φ₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective g₂
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Scheme.Hom.comp_base,
    TopCat.coe_comp, Function.comp_apply, Scheme.fromSpecResidueField_apply] at h
  subst h
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at h₁ h₂ ⊢
  suffices hφ : φ₁ = φ₂ by rw [hφ]

  set ψ := Spec.preimage (Y.fromSpecResidueField y₁ ≫ p) with hψ
  have hψ' : Spec.map ψ = Y.fromSpecResidueField y₁ ≫ p := Spec.map_preimage _
  have e₁ : ψ ≫ φ₁ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ', Spec.map_id, ← h₁, Category.assoc]
  have e₂ : ψ ≫ φ₂ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ', Spec.map_id, ← h₂, Category.assoc]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  have hinj : Function.Injective φ₁.hom := φ₁.hom.injective
  have hc : ψ.hom (φ₁.hom c) = c := by
    apply hinj
    change (ψ ≫ φ₁).hom (φ₁.hom c) = φ₁.hom c
    rw [e₁]; rfl
  calc φ₁.hom c = (ψ ≫ φ₂).hom (φ₁.hom c) := by rw [e₂]; rfl
    _ = φ₂.hom (ψ.hom (φ₁.hom c)) := rfl
    _ = φ₂.hom c := by rw [hc]

theorem prod_eq_iInf_of_pairwise {X : Scheme.{u}} {ι : Type*} [Fintype ι]
    (I : ι → X.IdealSheafData) (h : Pairwise fun i j => I i ⊔ I j = ⊤) :
    ∏ i, I i = ⨅ i, I i := by
  classical
  apply Scheme.IdealSheafData.ext
  funext U
  have hprod : (∏ i, I i).ideal U = ∏ i, (I i).ideal U := by
    induction (Finset.univ : Finset ι) using Finset.cons_induction with
    | empty => simp [Ideal.one_eq_top]
    | cons i s hi ih => rw [Finset.prod_cons, Finset.prod_cons, ← ih]; rfl
  rw [hprod, Scheme.IdealSheafData.ideal_iInf, iInf_apply,
    Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp
  · intro i _ j _ hij
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    have := congrArg (fun J : X.IdealSheafData => J.ideal U) (h hij)
    simpa using this

section GroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem val_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  conv_lhs => rw [← hx]
  rw [← G.nsmul_natural f t x.1 x.2 n]
  rfl

theorem val_one (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id _)]
  rfl

theorem nsmul_eq_one_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t n x = G.one t ↔ x.1 ≫ G.schemeNsmul n = t ≫ (G.one (𝟙 _)).1 := by
  rw [← val_nsmul, ← val_one]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem schemeHomOverComp_nsmul (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.nsmul t n x) = G.nsmul t' n (schemeHomOverComp ψ hψ x) :=
  G.nsmul_natural t t' ψ hψ n x

end GroupLaw

section Eval

variable {K : Type u} [CommRing K] (V : WeierstrassCurve.Projective K)
  (G : RelativeGroupLaw K (projModelStrCR V))
  (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra K F],
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR V) ≃
      (V.baseChange F).toAffine.Point)

theorem ev_one (hev : IsPointsEval V G ev) (F : Type u) [Field F] [DecidableEq F] [Algebra K F] :
    ev F (G.one _) = 0 := by
  have h := hev.1 F (G.one _) (G.one _)
  rw [G.one_mul] at h
  have h' : ev F (G.one _) + ev F (G.one _) = ev F (G.one _) + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

theorem ev_nsmul (hev : IsPointsEval V G ev) (F : Type u) [Field F] [DecidableEq F] [Algebra K F]
    (n : ℕ) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR V)) :
    ev F (G.nsmul _ n x) = n • ev F x := by
  induction n with
  | zero => rw [G.nsmul_zero, ev_one V G ev hev, zero_smul]
  | succ n ih => rw [G.nsmul_succ, hev.1, ih, succ_nsmul]

end Eval

section Bridge

variable {K : Type u} [CommRing K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

def toGRJ (G : RelativeGroupLaw K f) : GoodReductionJacobian.RelativeGroupLaw K f where
  mul := G.mul
  one := G.one
  inv := G.inv
  mul_assoc := G.mul_assoc
  one_mul := G.one_mul
  mul_one := G.mul_one
  inv_mul_cancel := G.inv_mul_cancel
  mul_natural := G.mul_natural

theorem toGRJ_schemeNsmul (G : RelativeGroupLaw K f) (n : ℕ) :
    (toGRJ G).schemeNsmul n = G.schemeNsmul n := rfl

theorem toGRJ_schemeKer (G : RelativeGroupLaw K f) (n : ℕ) :
    (toGRJ G).schemeKer n = G.schemeKer n := rfl

end Bridge

end P2MKcDrin

open P2MKcDrin

set_option maxHeartbeats 1600000 in
theorem solution
    {K : Type} [Field K] (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ)
    (G : WeierstrassProjModel.RelativeGroupLaw K (WeierstrassProjModel.projModelStrCR W))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (WeierstrassProjModel.projModelStrCR W) ≃ (W.baseChange F).toAffine.Point)
    (hev : WeierstrassProjModel.IsPointsEval W G ev)
    (q : ℕ) (hqK : (q : K) ≠ 0)
    (P Q : WeierstrassCurve.DrinfeldGlobal.Section W)
    (hP : G.nsmul (𝟙 _) q P = G.one (𝟙 _)) (hQ : G.nsmul (𝟙 _) q Q = G.one (𝟙 _))
    (hinj : ∀ a b a' b' : ℕ, a < q → b < q → a' < q → b' < q →
      WeierstrassCurve.DrinfeldGlobal.linComb G P Q a b =
        WeierstrassCurve.DrinfeldGlobal.linComb G P Q a' b' → a = a' ∧ b = b') :
    WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis G q P Q := by
  classical

  have hq0 : q ≠ 0 := by rintro rfl; exact hqK (by simp)
  haveI hEll : WeierstrassCurve.IsElliptic W := ⟨hΔ⟩
  have hprop := WeierstrassProjModel.projModelStrCR_isProper W
  haveI : IsSeparated (projModelStrCR W) := inferInstance
  haveI : LocallyOfFiniteType (projModelStrCR W) := inferInstance

  haveI : Flat (G.schemeNsmul q) :=
    WeierstrassProjModel.schemeNsmul_flat_of_isPointsEval_of_isElliptic W G ev hev q hq0
  have hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (projModelStrCR W)), G.mul t x y = G.mul t y x :=
    fun t x y => WeierstrassProjModel.mul_comm_of_isPointsEval K W G ev hev t x y
  have hred : IsReduced (G.schemeKer q) := by
    haveI : Flat ((toGRJ G).schemeNsmul q) := ‹Flat (G.schemeNsmul q)›
    exact GoodReductionJacobian.RelativeGroupLaw.isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit
      (R := K) (K := K) (fun _ _ h => h) (toGRJ G) (fun t x y => hcomm t x y) q
      (Ne.isUnit hqK)

  have htors : ∀ a' b' : ℕ, G.nsmul (𝟙 _) q (linComb G P Q a' b') = G.one (𝟙 _) := by
    letI grp : CommGroup (Section W) :=
      { G.pointGroup (𝟙 _) with mul_comm := fun x y => hcomm (𝟙 _) x y }
    have hpow : ∀ (n : ℕ) (x : Section W), G.nsmul (𝟙 _) n x = x ^ n := by
      intro n x
      induction n with
      | zero => rfl
      | succ n ih => rw [G.nsmul_succ, ih, pow_succ]; rfl
    intro a' b'
    have hP' : P ^ q = 1 := by rw [← hpow]; exact hP
    have hQ' : Q ^ q = 1 := by rw [← hpow]; exact hQ
    show G.nsmul (𝟙 _) q (G.mul _ (G.nsmul _ a' P) (G.nsmul _ b' Q)) = G.one _
    rw [hpow, hpow, hpow]
    show (P ^ a' * Q ^ b') ^ q = 1
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a' q, mul_comm b' q, pow_mul, pow_mul, hP', hQ',
      one_pow, one_pow, one_mul]

  unfold IsDrinfeldBasis basisDivisor torsionIdeal
  rw [prodKerGraph_eq_prod]

  set e : Spec (CommRingCat.of K) ⟶ projModelCR W := (G.one (𝟙 _)).1 with he_def
  have he : e ≫ projModelStrCR W = 𝟙 _ := (G.one (𝟙 _)).2
  haveI : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ projModelStrCR W) := by rw [he]; infer_instance
    exact .of_comp e (projModelStrCR W)
  have hred' : IsReduced (pullback (G.schemeNsmul q) e) := hred

  have hφfst : (toPullbackId (W := W)) ≫ pullback.fst (projModelStrCR W) (𝟙 _) = 𝟙 _ :=
    pullback.lift_fst _ _ _
  have hφsnd : (toPullbackId (W := W)) ≫ pullback.snd (projModelStrCR W) (𝟙 _) = projModelStrCR W :=
    pullback.lift_snd _ _ _
  haveI : IsIso (toPullbackId (W := W)) := by
    have : IsIso (toPullbackId (W := W) ≫ pullback.fst (projModelStrCR W) (𝟙 _)) := by
      rw [hφfst]; infer_instance
    exact IsIso.of_isIso_comp_right (toPullbackId (W := W)) (pullback.fst (projModelStrCR W) (𝟙 _))

  obtain ⟨ι, hι_def⟩ : ∃ ι : pullback (G.schemeNsmul q) e ⟶ pullback (projModelStrCR W) (𝟙 _),
      ι = pullback.fst (G.schemeNsmul q) e ≫ toPullbackId (W := W) := ⟨_, rfl⟩
  haveI hιci : IsClosedImmersion ι := by rw [hι_def]; infer_instance
  rw [← hι_def]

  obtain ⟨g, hg_def⟩ : ∃ g : Fin (q * q) → (Spec (CommRingCat.of K) ⟶ pullback (projModelStrCR W) (𝟙 _)),
      g = fun i => graphOver (projModelStrCR W) (basisTuple G q P Q i) (basisTuple_over G q P Q i) :=
    ⟨_, rfl⟩
  have hg_apply : ∀ i,
      graphOver (projModelStrCR W) (basisTuple G q P Q i) (basisTuple_over G q P Q i) = g i :=
    fun i => by rw [hg_def]
  simp only [hg_apply]
  haveI hgci : ∀ i, IsClosedImmersion (g i) := fun i => by rw [← hg_apply]; infer_instance
  have hg : ∀ i, g i = (linComb G P Q (i.val / q) (i.val % q)).1 ≫ toPullbackId (W := W) := by
    intro i
    rw [← hg_apply]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, hφfst, Category.comp_id]; rfl
    · rw [graphOver_snd, Category.assoc, hφsnd]; exact (basisTuple_over G q P Q i).symm
  have hg_snd : ∀ i, g i ≫ pullback.snd (projModelStrCR W) (𝟙 _) = 𝟙 _ := fun i => by
    rw [← hg_apply, graphOver_snd]

  have hkfst_f : pullback.fst (G.schemeNsmul q) e ≫ projModelStrCR W = pullback.snd (G.schemeNsmul q) e := by
    calc pullback.fst (G.schemeNsmul q) e ≫ projModelStrCR W
          = pullback.fst (G.schemeNsmul q) e ≫ G.schemeNsmul q ≫ projModelStrCR W := by
            rw [G.schemeNsmul_over]
      _ = (pullback.fst (G.schemeNsmul q) e ≫ G.schemeNsmul q) ≫ projModelStrCR W :=
            (Category.assoc _ _ _).symm
      _ = (pullback.snd (G.schemeNsmul q) e ≫ e) ≫ projModelStrCR W := by rw [pullback.condition]
      _ = pullback.snd (G.schemeNsmul q) e := by rw [Category.assoc, he, Category.comp_id]
  have hrange_g : ∀ i, Set.range (g i) ⊆ Set.range ι := by
    intro i
    have htor : (linComb G P Q (i.val / q) (i.val % q)).1 ≫ G.schemeNsmul q = 𝟙 _ ≫ e := by
      rw [he_def]; exact (nsmul_eq_one_iff G (𝟙 _) q _).mp (htors _ _)
    rintro _ ⟨s, rfl⟩
    refine ⟨pullback.lift _ (𝟙 _) htor s, ?_⟩
    rw [hg i, ← Scheme.Hom.comp_apply, hι_def, ← Category.assoc, pullback.lift_fst]

  have hsep : ∀ i j : Fin (q * q), (∃ s, g i s = g j s) → i = j := by
    rintro i j ⟨s, hs⟩
    have hgg : g i = g j :=
      section_eq_of_apply_eq (pullback.snd (projModelStrCR W) (𝟙 _)) (g i) (g j) (hg_snd i) (hg_snd j) s hs
    have haa := congrArg (· ≫ pullback.fst (projModelStrCR W) (𝟙 _)) hgg
    simp only [hg, Category.assoc, hφfst, Category.comp_id] at haa
    have hlin : linComb G P Q (i.val / q) (i.val % q) = linComb G P Q (j.val / q) (j.val % q) :=
      Subtype.ext haa
    have hiq : i.val / q < q := Nat.div_lt_of_lt_mul i.isLt
    have hjq : j.val / q < q := Nat.div_lt_of_lt_mul j.isLt
    obtain ⟨h1, h2⟩ := hinj _ _ _ _ hiq (Nat.mod_lt _ (Nat.pos_of_ne_zero hq0)) hjq
      (Nat.mod_lt _ (Nat.pos_of_ne_zero hq0)) hlin
    apply Fin.ext
    rw [← Nat.div_add_mod i.val q, ← Nat.div_add_mod j.val q, h1, h2]

  have hrange_ι : Set.range ι ⊆ ⋃ i, Set.range (g i) := by
    rintro _ ⟨z, rfl⟩

    let κ : Type := (pullback (G.schemeNsmul q) e).residueField z
    let σ : Spec (CommRingCat.of κ) ⟶ pullback (G.schemeNsmul q) e :=
      (pullback (G.schemeNsmul q) e).fromSpecResidueField z
    let t₀ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of K) := σ ≫ pullback.snd (G.schemeNsmul q) e
    letI : Algebra K κ := (Spec.preimage t₀).hom.toAlgebra
    have ht : Spec.map (CommRingCat.ofHom (algebraMap K κ)) = t₀ := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    set t := Spec.map (CommRingCat.ofHom (algebraMap K κ)) with ht_def

    let Pz : SchemeHomOver t (projModelStrCR W) :=
      ⟨σ ≫ pullback.fst (G.schemeNsmul q) e, by rw [Category.assoc, hkfst_f, ht]⟩
    have hPz : G.nsmul t q Pz = G.one t := by
      rw [nsmul_eq_one_iff]
      show (σ ≫ pullback.fst (G.schemeNsmul q) e) ≫ G.schemeNsmul q = t ≫ (G.one (𝟙 _)).1
      rw [Category.assoc, pullback.condition, ← Category.assoc, ht, ← he_def]

    have htt : t ≫ 𝟙 _ = t := Category.comp_id _
    let bc : Section W → SchemeHomOver t (projModelStrCR W) := fun x => schemeHomOverComp t htt x
    have hbc_inj : Function.Injective bc := by
      intro x y hxy
      have h1 : t ≫ x.1 = t ≫ y.1 := congrArg Subtype.val hxy
      haveI : Surjective t := ⟨fun s => ⟨default, Subsingleton.elim _ _⟩⟩
      apply Subtype.ext
      exact ext_of_isDominant_of_isSeparated (projModelStrCR W) (x.2.trans y.2.symm) t h1
    have hbc_nsmul : ∀ (n : ℕ) (x : Section W), bc (G.nsmul _ n x) = G.nsmul t n (bc x) :=
      fun n x => schemeHomOverComp_nsmul G (𝟙 _) t t htt n x
    have hbc_one : bc (G.one _) = G.one t := G.one_natural (𝟙 _) t t htt

    haveI : (W.baseChange κ).IsElliptic :=
      ⟨by simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] using hΔ.map (algebraMap K κ)⟩
    have hqκ : (q : κ) ≠ 0 := by
      intro h0
      apply hqK
      apply (algebraMap K κ).injective
      rw [map_natCast, h0, map_zero]
    let pt : ℕ × ℕ → (W.baseChange κ).toAffine.Point := fun ab => ev κ (bc (linComb G P Q ab.1 ab.2))
    have hpt_tors : ∀ ab, q • pt ab = 0 := by
      intro ab
      show q • ev κ (bc (linComb G P Q ab.1 ab.2)) = 0
      rw [← ev_nsmul W G ev hev, ← hbc_nsmul, htors, hbc_one, ev_one W G ev hev]
    have hPz_tors : q • ev κ Pz = 0 := by
      rw [← ev_nsmul W G ev hev, hPz, ev_one W G ev hev]

    set S₀ : Finset ((W.baseChange κ).toAffine.Point) :=
      (Finset.range q ×ˢ Finset.range q).image pt with hS₀
    have hinjOn : Set.InjOn pt ↑(Finset.range q ×ˢ Finset.range q) := by
      rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ h12
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at h₁ h₂
      have h' : linComb G P Q a₁ b₁ = linComb G P Q a₂ b₂ := hbc_inj ((ev κ).injective h12)
      obtain ⟨rfl, rfl⟩ := hinj _ _ _ _ h₁.1 h₁.2 h₂.1 h₂.2 h'
      rfl
    have hcard : S₀.card = q * q := by
      rw [hS₀, Finset.card_image_of_injOn hinjOn, Finset.card_product, Finset.card_range]

    have hmem : ev κ Pz ∈ S₀ := by
      by_contra hnot
      have hle := WeierstrassCurve.Affine.Point.card_le_sq_of_forall_nsmul_eq_zero (W.baseChange κ) q hqκ
        (insert (ev κ Pz) S₀) (by
          intro R hR
          rcases Finset.mem_insert.mp hR with rfl | hR
          · exact hPz_tors
          · obtain ⟨ab, -, rfl⟩ := Finset.mem_image.mp hR
            exact hpt_tors ab)
      rw [Finset.card_insert_of_notMem hnot, hcard, sq] at hle
      exact Nat.lt_irrefl _ hle
    obtain ⟨⟨a₁, b₁⟩, hab, hEq⟩ := Finset.mem_image.mp hmem
    simp only [Finset.mem_product, Finset.mem_range] at hab
    have hPz_eq : bc (linComb G P Q a₁ b₁) = Pz := (ev κ).injective hEq
    have hval : t ≫ (linComb G P Q a₁ b₁).1 = σ ≫ pullback.fst (G.schemeNsmul q) e :=
      congrArg Subtype.val hPz_eq

    have hi_lt : a₁ * q + b₁ < q * q :=
      calc a₁ * q + b₁ < a₁ * q + q := Nat.add_lt_add_left hab.2 _
        _ = (a₁ + 1) * q := (Nat.succ_mul a₁ q).symm
        _ ≤ q * q := Nat.mul_le_mul_right q hab.1
    let i : Fin (q * q) := ⟨a₁ * q + b₁, hi_lt⟩
    have hi_div : i.val / q = a₁ := by
      show (a₁ * q + b₁) / q = a₁
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero hq0), Nat.div_eq_of_lt hab.2,
        zero_add]
    have hi_mod : i.val % q = b₁ := by
      show (a₁ * q + b₁) % q = b₁
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hab.2]
    refine Set.mem_iUnion.mpr ⟨i, ⟨default, ?_⟩⟩

    have hσ : σ default = z := Scheme.fromSpecResidueField_apply _ _
    have htpt : t default = (default : Spec (CommRingCat.of K)) := Subsingleton.elim _ _
    rw [hg i, hi_div, hi_mod, hι_def, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hσ,
      ← Scheme.Hom.comp_apply σ, ← hval, Scheme.Hom.comp_apply, htpt]

  have hrange : Set.range ι = ⋃ i, Set.range (g i) :=
    Set.Subset.antisymm hrange_ι (Set.iUnion_subset hrange_g)
  let V : Fin (q * q) → TopologicalSpace.Closeds ↥(pullback (projModelStrCR W) (𝟙 (Spec (CommRingCat.of K)))) :=
    fun i => ⟨Set.range (g i), (g i).isClosedEmbedding.isClosed_range⟩
  have hVsup : (⨆ i, V i) = ⟨Set.range ι, ι.isClosedEmbedding.isClosed_range⟩ := by
    apply le_antisymm
    · exact iSup_le fun i => (hrange_g i : (V i : Set _) ⊆ Set.range ι)
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hrange ▸ hx : x ∈ ⋃ i, Set.range (g i))
      exact (le_iSup V i : (V i : Set _) ⊆ _) hi
  have hker_g : ∀ i, (g i).ker = Scheme.IdealSheafData.vanishingIdeal (V i) := fun i =>
    ker_eq_vanishingIdeal_range (g i)
  have hker_ι : ι.ker = ⨅ i, (g i).ker := by
    haveI : IsReduced (pullback (G.schemeNsmul q) e) := hred'
    rw [ker_eq_vanishingIdeal_range ι, ← hVsup, Scheme.IdealSheafData.vanishingIdeal_iSup]
    exact iInf_congr fun i => (hker_g i).symm

  have hsupp_g : ∀ i, ((g i).ker.support : Set _) = Set.range (g i) := fun i => by
    rw [Scheme.Hom.support_ker, (g i).isClosedEmbedding.isClosed_range.closure_eq]
  have hpair : Pairwise fun i j => (g i).ker ⊔ (g j).ker = ⊤ := by
    intro i j hij
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_sup]
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_inf, TopologicalSpace.Closeds.coe_bot, hsupp_g, hsupp_g,
      Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨s, hs⟩, ⟨s', hs'⟩⟩
    have hss : s' = s := Subsingleton.elim _ _
    exact hij (hsep i j ⟨s, by rw [hs, ← hs', hss]⟩)

  rw [hker_ι]
  exact prod_eq_iInf_of_pairwise _ hpair

end S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj (solution)

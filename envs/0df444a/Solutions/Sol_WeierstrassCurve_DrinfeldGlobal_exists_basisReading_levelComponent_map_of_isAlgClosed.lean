-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_basisReading_levelComponent_map_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0f2ba7fa-bbcf-5d9e-afec-145cb6e378d6

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_basisReading_levelComponent_map_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace P2MKcDrinRead

theorem exists_mem_support_of_mem_support_prod {X : Scheme.{u}} {ι : Type*} [Fintype ι]
    (I : ι → X.IdealSheafData) {x : X} (hx : x ∈ (∏ i, I i).support) : ∃ i, x ∈ (I i).support := by
  classical
  suffices h : ∀ s : Finset ι, x ∈ (∏ i ∈ s, I i).support → ∃ i ∈ s, x ∈ (I i).support by
    obtain ⟨i, -, hi⟩ := h Finset.univ hx
    exact ⟨i, hi⟩
  intro s
  induction s using Finset.cons_induction with
  | empty =>
    intro h
    rw [Finset.prod_empty] at h
    change x ∈ ((⊤ : X.IdealSheafData).support : Set X) at h
    rw [Scheme.IdealSheafData.support_top] at h
    exact absurd h (Set.notMem_empty x)
  | cons i s hi ih =>
    intro h
    rw [Finset.prod_cons, Scheme.IdealSheafData.support_mul] at h
    change x ∈ ((I i).support : Set X) ∪ ((∏ j ∈ s, I j).support : Set X) at h
    rcases h with h | h
    · exact ⟨i, Finset.mem_cons_self i s, h⟩
    · obtain ⟨j, hj, hj'⟩ := ih h
      exact ⟨j, Finset.mem_cons_of_mem hj, hj'⟩

theorem eq_comp_of_apply_eq {K F : Type u} [Field K] [Field F] [Algebra K F] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of K)) (s : Spec (CommRingCat.of K) ⟶ Y) (hs : s ≫ p = 𝟙 _)
    (x : Spec (CommRingCat.of F) ⟶ Y)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K F)))
    (a : Spec (CommRingCat.of F)) (b : Spec (CommRingCat.of K)) (h : x a = s b) :
    x = Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ s := by
  obtain ⟨⟨y, φx⟩, rfl⟩ := (Scheme.SpecToEquivOfField F Y).symm.surjective x
  obtain ⟨⟨y', φs⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective s
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Scheme.Hom.comp_base,
    TopCat.coe_comp, Function.comp_apply, Scheme.fromSpecResidueField_apply] at h
  subst h
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hs hx ⊢

  set ψ := Spec.preimage (Y.fromSpecResidueField y ≫ p) with hψ
  have hψ' : Spec.map ψ = Y.fromSpecResidueField y ≫ p := Spec.map_preimage _
  have e₁ : ψ ≫ φs = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ', Spec.map_id, ← hs, Category.assoc]
  have e₂ : ψ ≫ φx = CommRingCat.ofHom (algebraMap K F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ', ← hx, Category.assoc]
  suffices hφ : φx = φs ≫ CommRingCat.ofHom (algebraMap K F) by
    rw [hφ, Spec.map_comp, Category.assoc]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  have hinj : Function.Injective φs.hom := φs.hom.injective
  have hc : ψ.hom (φs.hom c) = c := by
    apply hinj
    change (ψ ≫ φs).hom (φs.hom c) = φs.hom c
    rw [e₁]; rfl
  calc φx.hom c = φx.hom (ψ.hom (φs.hom c)) := by rw [hc]
    _ = (ψ ≫ φx).hom (φs.hom c) := rfl
    _ = (CommRingCat.ofHom (algebraMap K F)).hom (φs.hom c) := by rw [e₂]
    _ = (φs ≫ CommRingCat.ofHom (algebraMap K F)).hom c := rfl

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

theorem mul_val_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)}
    (h : t = t') (x y : SchemeHomOver t f) :
    (G.mul t x y).1 = (G.mul t' ⟨x.1, h ▸ x.2⟩ ⟨y.1, h ▸ y.2⟩).1 := by
  subst h; rfl

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

section Coefficient

variable {T T' T'' : Type u} [CommRing T] [CommRing T'] [CommRing T'']

theorem coefficientHom_unique (V : WeierstrassCurve.Projective T) (g : T →+* T')
    (ψ ψ' : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map g))
    (h : IsCoefficientHom V g ψ) (h' : IsCoefficientHom V g ψ') : ψ = ψ' := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a => exact (h.1 a).trans (h'.1 a).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    exact (h.2 i).trans (h'.2 i).symm

theorem isCoefficientHom_comp (V : WeierstrassCurve.Projective T) (g : T →+* T') (g' : T' →+* T'')
    (ψ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map g)) (h : IsCoefficientHom V g ψ)
    (ψ' : projModelGradingCR (V.map g) →+*ᵍ projModelGradingCR ((V.map g).map g'))
    (h' : IsCoefficientHom (V.map g) g' ψ') :
    IsCoefficientHom V (g'.comp g) (show projModelGradingCR V →+*ᵍ projModelGradingCR (V.map (g'.comp g)) from
      ψ'.comp ψ) := by
  refine ⟨fun a => ?_, fun i => ?_⟩
  · show ψ' (ψ (cls V (MvPolynomial.C a))) = _
    rw [h.1 a, h'.1 (g a)]
    rfl
  · show ψ' (ψ (cls V (MvPolynomial.X i))) = _
    rw [h.2 i, h'.2 i]
    rfl

theorem projMap_eq_eqToHom_comp_projMap (V : WeierstrassCurve.Projective T) {g g' : T →+* T'} (hg : g = g')
    (ψ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map g))
    (hψ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map ψ)
    (hc : IsCoefficientHom V g ψ)
    (ψ' : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map g'))
    (hψ' : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map g')) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map ψ')
    (hc' : IsCoefficientHom V g' ψ')
    (e : projModelCR (V.map g) = projModelCR (V.map g')) :
    Proj.map ψ hψ = eqToHom e ≫ Proj.map ψ' hψ' := by
  subst hg
  obtain rfl : ψ = ψ' := coefficientHom_unique V g ψ ψ' hc hc'
  rw [eqToHom_refl, Category.id_comp]

end Coefficient

theorem nsmul_eq_one_and_linComb_injective_of_isDrinfeldBasis
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve.Projective K)
    (hΔ : IsUnit W.Δ) (G : RelativeGroupLaw K (projModelStrCR W))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W) ≃
        (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev)
    (q : ℕ) (hq2 : 2 ≤ q) (hqK : (q : K) ≠ 0) (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q) :
    G.nsmul (𝟙 _) q P = G.one (𝟙 _) ∧ G.nsmul (𝟙 _) q Q = G.one (𝟙 _) ∧
      ∀ a b a' b' : ℕ, a < q → b < q → a' < q → b' < q →
        linComb G P Q a b = linComb G P Q a' b' → a = a' ∧ b = b' := by
  classical

  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_two hq2
  haveI hEll : WeierstrassCurve.IsElliptic W := ⟨hΔ⟩
  have hprop := WeierstrassProjModel.projModelStrCR_isProper W
  haveI : IsSeparated (projModelStrCR W) := inferInstance

  letI grp : Group (Section W) := G.pointGroup (𝟙 _)
  have hpow : ∀ (n : ℕ) (x : Section W), G.nsmul (𝟙 _) n x = x ^ n := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, ih, pow_succ]; rfl
  have hlin : ∀ a b : ℕ, linComb G P Q a b = P ^ a * Q ^ b := by
    intro a b
    show G.mul (𝟙 _) (G.nsmul (𝟙 _) a P) (G.nsmul (𝟙 _) b Q) = P ^ a * Q ^ b
    rw [hpow, hpow]
    rfl

  let sec : Fin (q * q) → Section W := fun i => linComb G P Q (i.val / q) (i.val % q)

  set e : Spec (CommRingCat.of K) ⟶ projModelCR W := (G.one (𝟙 _)).1 with he_def
  have he : e ≫ projModelStrCR W = 𝟙 _ := (G.one (𝟙 _)).2

  have hφfst : (toPullbackId (W := W)) ≫ pullback.fst (projModelStrCR W) (𝟙 _) = 𝟙 _ :=
    pullback.lift_fst _ _ _

  obtain ⟨ι, hι_def⟩ : ∃ ι : pullback (G.schemeNsmul q) e ⟶ pullback (projModelStrCR W) (𝟙 _),
      ι = pullback.fst (G.schemeNsmul q) e ≫ toPullbackId (W := W) := ⟨_, rfl⟩

  obtain ⟨gr, hgr_def⟩ :
      ∃ gr : Fin (q * q) → (Spec (CommRingCat.of K) ⟶ pullback (projModelStrCR W) (𝟙 _)),
      gr = fun i => graphOver (projModelStrCR W) (basisTuple G q P Q i) (basisTuple_over G q P Q i) :=
    ⟨_, rfl⟩
  have hgr_apply : ∀ i,
      graphOver (projModelStrCR W) (basisTuple G q P Q i) (basisTuple_over G q P Q i) = gr i :=
    fun i => by rw [hgr_def]
  haveI hgrci : ∀ i, IsClosedImmersion (gr i) := fun i => by rw [← hgr_apply]; infer_instance
  have hgr_fst : ∀ i, gr i ≫ pullback.fst (projModelStrCR W) (𝟙 _) = (sec i).1 := fun i => by
    rw [← hgr_apply, graphOver_fst]
    rfl

  have hDB : ∏ i, (gr i).ker = ι.ker := by
    have h := hPQ
    unfold IsDrinfeldBasis basisDivisor torsionIdeal at h
    rw [prodKerGraph_eq_prod] at h
    simp only [hgr_apply] at h
    rw [hι_def, he_def]
    exact h

  have hA : ∀ z : ↥(pullback (G.schemeNsmul q) e), ∃ i : Fin (q * q),
      (pullback.fst (G.schemeNsmul q) e) z = (sec i).1 default := by
    intro z
    have h1 : ι z ∈ (ι.ker.support : Set _) := ι.range_subset_ker_support ⟨z, rfl⟩
    rw [← hDB] at h1
    obtain ⟨i, hi⟩ := exists_mem_support_of_mem_support_prod _ h1
    have hi' : ι z ∈ closure (Set.range (gr i)) := by
      rw [← (gr i).support_ker]; exact hi
    rw [(gr i).isClosedEmbedding.isClosed_range.closure_eq] at hi'
    obtain ⟨s, hs⟩ := hi'
    refine ⟨i, ?_⟩
    have hs' : (gr i ≫ pullback.fst (projModelStrCR W) (𝟙 _)) s =
        (ι ≫ pullback.fst (projModelStrCR W) (𝟙 _)) z := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hs]
    rw [hgr_fst, hι_def, Category.assoc, hφfst, Category.comp_id] at hs'
    rw [← hs', Subsingleton.elim s default]

  set t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K K)) with ht_def

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

  have hB : ∀ x : SchemeHomOver t (projModelStrCR W), G.nsmul t q x = G.one t → ∃ i, bc (sec i) = x := by
    intro x hx
    have hx' : x.1 ≫ G.schemeNsmul q = t ≫ e := by
      rw [he_def]; exact (nsmul_eq_one_iff G t q x).mp hx
    let z : Spec (CommRingCat.of K) ⟶ pullback (G.schemeNsmul q) e := pullback.lift x.1 t hx'
    obtain ⟨i, hi⟩ := hA (z default)
    refine ⟨i, ?_⟩
    apply Subtype.ext
    symm
    show x.1 = t ≫ (sec i).1
    apply eq_comp_of_apply_eq (projModelStrCR W) (sec i).1 (sec i).2 x.1 x.2 default default
    rw [← hi, ← Scheme.Hom.comp_apply, pullback.lift_fst]

  let Pt : Type u := (W.baseChange K).toAffine.Point
  let Φ : Fin (q * q) → Pt := fun i => ev K (bc (sec i))
  have hsurj : ∀ T : Pt, q • T = 0 → ∃ i, Φ i = T := by
    intro T hT
    have hx : G.nsmul t q ((ev K).symm T) = G.one t := by
      apply (ev K).injective
      rw [ev_nsmul W G ev hev, Equiv.apply_symm_apply, hT, ev_one W G ev hev]
    obtain ⟨i, hi⟩ := hB _ hx
    exact ⟨i, by simp only [Φ, hi, Equiv.apply_symm_apply]⟩
  have hcount : Nat.card ↥(Submodule.torsionBy ℤ Pt (q : ℤ)) = q ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) W hqK

  set S : Finset Pt := Finset.univ.image Φ with hS
  have hsub : ((Submodule.torsionBy ℤ Pt (q : ℤ)) : Set Pt) ⊆ (S : Set Pt) := by
    intro T hT
    have hT' : q • T = 0 := by
      have h := (Submodule.mem_torsionBy_iff (q : ℤ) T).mp hT
      rwa [natCast_zsmul] at h
    obtain ⟨i, rfl⟩ := hsurj T hT'
    simp [hS]
  have hScard_ge : q ^ 2 ≤ S.card := by
    rw [← hcount, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet S)
  have hScard_le : S.card ≤ q * q :=
    Finset.card_image_le.trans (by simp)
  have hScard : S.card = q * q := le_antisymm hScard_le (by rw [← sq]; exact hScard_ge)
  have hΦinj : Function.Injective Φ := by
    have h : S.card = (Finset.univ : Finset (Fin (q * q))).card := by rw [hScard]; simp
    have hinjOn := Finset.card_image_iff.mp h
    intro i j hij
    exact hinjOn (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij
  have hsec_inj : Function.Injective sec := fun i j hij => hΦinj (by simp only [Φ, hij])

  have hSeq : ((Submodule.torsionBy ℤ Pt (q : ℤ)) : Set Pt) = (S : Set Pt) := by
    apply Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet S)
    rw [Set.ncard_coe_finset, hScard, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcount, sq]
  have hsec_tors : ∀ i, sec i ^ q = 1 := by
    intro i
    have hmem : Φ i ∈ (S : Set Pt) := by simp [hS]
    rw [← hSeq] at hmem
    have h1 : q • Φ i = 0 := by
      have h := (Submodule.mem_torsionBy_iff (q : ℤ) (Φ i)).mp hmem
      rwa [natCast_zsmul] at h
    have h2 : G.nsmul t q (bc (sec i)) = G.one t := by
      apply (ev K).injective
      rw [ev_nsmul W G ev hev, ev_one W G ev hev]
      exact h1
    rw [← hbc_nsmul, ← hbc_one] at h2
    have h3 := hbc_inj h2
    rw [hpow] at h3
    exact h3

  have hqlt : q < q * q := by nlinarith
  have h1lt : 1 < q * q := by nlinarith
  have hPsec : sec ⟨q, hqlt⟩ = P := by
    show linComb G P Q (q / q) (q % q) = P
    rw [Nat.div_self hqpos, Nat.mod_self, hlin, pow_one, pow_zero, mul_one]
  have hQsec : sec ⟨1, h1lt⟩ = Q := by
    show linComb G P Q (1 / q) (1 % q) = Q
    rw [Nat.div_eq_of_lt hq2, Nat.mod_eq_of_lt hq2, hlin, pow_zero, pow_one, one_mul]
  have hPq : P ^ q = 1 := by rw [← hPsec]; exact hsec_tors _
  have hQq : Q ^ q = 1 := by rw [← hQsec]; exact hsec_tors _
  refine ⟨by rw [hpow]; exact hPq, by rw [hpow]; exact hQq, ?_⟩
  intro a b a' b' ha hb ha' hb' hab

  have idx_lt : ∀ {c d : ℕ}, c < q → d < q → c * q + d < q * q := fun {c d} hc hd =>
    calc c * q + d < c * q + q := Nat.add_lt_add_left hd _
      _ = (c + 1) * q := (Nat.succ_mul c q).symm
      _ ≤ q * q := Nat.mul_le_mul_right q hc
  have idx_div : ∀ {c d : ℕ}, d < q → (c * q + d) / q = c := fun {c d} hd => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hqpos, Nat.div_eq_of_lt hd, zero_add]
  have idx_mod : ∀ {c d : ℕ}, d < q → (c * q + d) % q = d := fun {c d} hd => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
  have hseq : sec ⟨a * q + b, idx_lt ha hb⟩ = sec ⟨a' * q + b', idx_lt ha' hb'⟩ := by
    show linComb G P Q ((a * q + b) / q) ((a * q + b) % q) =
      linComb G P Q ((a' * q + b') / q) ((a' * q + b') % q)
    rw [idx_div hb, idx_mod hb, idx_div hb', idx_mod hb']
    exact hab
  have hidx : a * q + b = a' * q + b' := congrArg Fin.val (hsec_inj hseq)
  have hdiv := congrArg (· / q) hidx
  have hmod := congrArg (· % q) hidx
  simp only [idx_div hb, idx_div hb', idx_mod hb, idx_mod hb'] at hdiv hmod
  exact ⟨hdiv, hmod⟩

section Cast

variable {T : Type u} [CommRing T]

noncomputable def castSec {W W' : WeierstrassCurve.Projective T} (h : W = W') (s : Section W) : Section W' :=
  ⟨s.1 ≫ eqToHom (congrArg projModelCR h), by subst h; simpa using s.2⟩

theorem castSec_val {W W' : WeierstrassCurve.Projective T} (h : W = W') (s : Section W) :
    (castSec h s).1 = s.1 ≫ eqToHom (congrArg projModelCR h) := rfl

theorem castSec_rfl {W : WeierstrassCurve.Projective T} (s : Section W) : castSec rfl s = s :=
  Subtype.ext (by rw [castSec_val, eqToHom_refl, Category.comp_id])

end Cast

end P2MKcDrinRead

open P2MKcDrinRead

set_option hygiene false in

local notation "EΩ" => (WeierstrassCurve.map E (algebraMap K₀ Ω) : WeierstrassCurve.Projective Ω)

set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) (hq : 0 < q) (A : Type u) [CommRing A]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω] [Algebra A Ω]
    (K₀ : Type u) [Field K₀] [Algebra A K₀] [Algebra K₀ Ω] [IsScalarTower A K₀ Ω]
    (E : WeierstrassCurve K₀) [E.IsElliptic] :
    ∃ Θ : WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair Ω →
        (E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point,
      ∀ x : WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair Ω,
        WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel 𝒢 q (E.baseChange Ω) x →
        (q • (Θ x).1 = 0 ∧ q • (Θ x).2 = 0 ∧
          ∀ a b : ℤ, a • (Θ x).1 + b • (Θ x).2 = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧
        (∀ σ : Ω ≃ₐ[K₀] Ω,
          Θ (𝒯.map ((σ : Ω →ₐ[K₀] Ω).restrictScalars A) x) =
            (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ x).1,
              WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ x).2)) := by
  classical

  by_cases hq1 : q = 1
  · subst hq1
    refine ⟨fun _ => (0, 0), fun x _ => ⟨⟨by simp, by simp, fun a b _ => ⟨one_dvd a, one_dvd b⟩⟩, ?_⟩⟩
    intro σ
    simp only [map_zero]
  have hq2 : 2 ≤ q := by omega
  have hqΩ : (q : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'

  have hΔΩ : IsUnit (WeierstrassCurve.Δ EΩ) := (E.map (algebraMap K₀ Ω)).isUnit_Δ
  have hΔ₀ : IsUnit (E : WeierstrassCurve.Projective K₀).Δ := E.isUnit_Δ

  set G₀ : RelativeGroupLaw K₀ (projModelStrCR (E : WeierstrassCurve.Projective K₀)) := 𝒢 K₀ E hΔ₀ with hG₀
  set GΩ : RelativeGroupLaw Ω (projModelStrCR EΩ) := 𝒢 Ω EΩ hΔΩ with hGΩ

  obtain ⟨φ₀, hφ₀, hcoef₀⟩ := hCO K₀ Ω (IsScalarTower.toAlgHom A K₀ Ω) E
  change projModelGradingCR (E : WeierstrassCurve.Projective K₀) →+*ᵍ projModelGradingCR EΩ at φ₀
  change HomogeneousIdeal.irrelevant (projModelGradingCR EΩ) ≤
    (HomogeneousIdeal.irrelevant (projModelGradingCR (E : WeierstrassCurve.Projective K₀))).map φ₀ at hφ₀
  have hcoef₀' : IsCoefficientHom (E : WeierstrassCurve.Projective K₀) (algebraMap K₀ Ω) φ₀ := hcoef₀

  have hsqP : IsPullback (Proj.map φ₀ hφ₀) (projModelStrCR EΩ)
      (projModelStrCR (E : WeierstrassCurve.Projective K₀)) (Spec.map (CommRingCat.ofHom (algebraMap K₀ Ω))) :=
    WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom _ (algebraMap K₀ Ω) φ₀ hφ₀ hcoef₀'
  have hsq : Proj.map φ₀ hφ₀ ≫ projModelStrCR (E : WeierstrassCurve.Projective K₀) =
      projModelStrCR EΩ ≫ Spec.map (CommRingCat.ofHom (algebraMap K₀ Ω)) :=
    hsqP.w

  let push : Section EΩ → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K₀ Ω)))
      (projModelStrCR (E : WeierstrassCurve.Projective K₀)) := fun s =>
    ⟨s.1 ≫ Proj.map φ₀ hφ₀, by rw [Category.assoc, hsq, ← Category.assoc, s.2, Category.id_comp]⟩
  have hpush_val : ∀ s, (push s).1 = s.1 ≫ Proj.map φ₀ hφ₀ := fun _ => rfl
  have hpush_inj : Function.Injective push := by
    intro s s' h
    have h1 : s.1 ≫ Proj.map φ₀ hφ₀ = s'.1 ≫ Proj.map φ₀ hφ₀ := congrArg Subtype.val h
    apply Subtype.ext
    exact hsqP.hom_ext h1 (s.2.trans s'.2.symm)

  obtain ⟨ev₀, hev₀⟩ := h𝒢 K₀ E hΔ₀
  let R : Section EΩ → (E.baseChange Ω).toAffine.Point := fun s => ev₀ Ω (push s)
  have hR_def : ∀ s, R s = ev₀ Ω (push s) := fun _ => rfl
  have hR_inj : Function.Injective R := fun s s' h => hpush_inj ((ev₀ Ω).injective h)

  obtain ⟨χ, hχ, hχx, hχz⟩ := h𝒢O K₀ E hΔ₀
  obtain ⟨χ', hχ', hχ'x, hχ'z⟩ := h𝒢O Ω EΩ hΔΩ
  have h1 : (GΩ.one (𝟙 (Spec (CommRingCat.of Ω)))).1 ≫ Proj.map φ₀ hφ₀ =
      Spec.map (CommRingCat.ofHom (algebraMap K₀ Ω)) ≫ (G₀.one (𝟙 (Spec (CommRingCat.of K₀)))).1 :=
    WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_of_isOriginChartSection _ (algebraMap K₀ Ω) φ₀ hφ₀ hcoef₀'
      (G₀.one _) (GΩ.one _) χ hχ hχx hχz χ' hχ' hχ'x hχ'z

  have hpush_mul : ∀ s s' : Section EΩ,
      push (GΩ.mul (𝟙 _) s s') = G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap K₀ Ω))) (push s) (push s') := by
    intro s s'
    apply Subtype.ext
    rw [hpush_val]
    have hK5 := WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
      (E : WeierstrassCurve.Projective K₀) (algebraMap K₀ Ω) φ₀ hφ₀ hcoef₀' G₀ GΩ h1 hsq (𝟙 _) s s'
    exact hK5.trans (mul_val_congr G₀ (Category.id_comp _) _ _)
  have hR_mul : ∀ s s' : Section EΩ, R (GΩ.mul (𝟙 _) s s') = R s + R s' := by
    intro s s'
    rw [hR_def, hR_def, hR_def, hpush_mul]
    exact hev₀.1 Ω (push s) (push s')
  have hR_one : R (GΩ.one (𝟙 _)) = 0 := by
    have h := hR_mul (GΩ.one _) (GΩ.one _)
    rw [GΩ.one_mul] at h
    have h' : R (GΩ.one _) + R (GΩ.one _) = R (GΩ.one _) + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'

  have hR_gal : ∀ (σ : Ω ≃ₐ[K₀] Ω) (p : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K₀ Ω)))
      (projModelStrCR (E : WeierstrassCurve.Projective K₀))),
      ev₀ Ω (galTwist σ p) = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (ev₀ Ω p) :=
    fun σ p => hev₀.2 Ω σ p

  let Θ : RawDrinfeldPair Ω → (E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point := fun x =>
    if hx : x.curve = EΩ then (R (castSec hx x.P), R (castSec hx x.Q)) else (0, 0)
  have hΘ_pos : ∀ (x : RawDrinfeldPair Ω) (hx : x.curve = EΩ),
      Θ x = (R (castSec hx x.P), R (castSec hx x.Q)) := fun x hx => dif_pos hx
  refine ⟨Θ, ?_⟩

  rintro ⟨W, P, Q⟩ ⟨hxW, hΔ', hDB⟩
  change W = EΩ at hxW
  subst hxW

  change IsDrinfeldBasis GΩ q P Q at hDB
  have hΘx : Θ ⟨EΩ, P, Q⟩ = (R P, R Q) := by
    rw [hΘ_pos ⟨EΩ, P, Q⟩ rfl]
    show (R (castSec rfl P), R (castSec rfl Q)) = (R P, R Q)
    rw [castSec_rfl, castSec_rfl]

  obtain ⟨evΩ, hevΩ⟩ := h𝒢 Ω EΩ hΔΩ
  obtain ⟨hPq, hQq, hinj⟩ := nsmul_eq_one_and_linComb_injective_of_isDrinfeldBasis
    EΩ hΔΩ GΩ evΩ hevΩ q hq2 hqΩ P Q hDB

  letI grp : Group (Section EΩ) := GΩ.pointGroup (𝟙 _)
  have hpow : ∀ (n : ℕ) (x : Section EΩ), GΩ.nsmul (𝟙 _) n x = x ^ n := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih => rw [GΩ.nsmul_succ, ih, pow_succ]; rfl
  have hlin : ∀ a b : ℕ, linComb GΩ P Q a b = P ^ a * Q ^ b := by
    intro a b
    show GΩ.mul (𝟙 _) (GΩ.nsmul (𝟙 _) a P) (GΩ.nsmul (𝟙 _) b Q) = P ^ a * Q ^ b
    rw [hpow, hpow]
    rfl
  have hPq' : P ^ q = 1 := by rw [← hpow]; exact hPq
  have hQq' : Q ^ q = 1 := by rw [← hpow]; exact hQq
  have hR_mul' : ∀ s s' : Section EΩ, R (s * s') = R s + R s' := fun s s' => hR_mul s s'
  have hR_one' : R (1 : Section EΩ) = 0 := hR_one

  let Rh : Section EΩ →* Multiplicative (E.baseChange Ω).toAffine.Point :=
    { toFun := fun s => Multiplicative.ofAdd (R s)
      map_one' := by rw [hR_one']; rfl
      map_mul' := fun s s' => by rw [hR_mul']; rfl }
  have hRh : ∀ s, Rh s = Multiplicative.ofAdd (R s) := fun _ => rfl
  have hR_zpow : ∀ (n : ℤ) (s : Section EΩ), R (s ^ n) = n • R s := by
    intro n s
    have h := map_zpow Rh s n
    rw [hRh, hRh] at h
    exact Multiplicative.ofAdd.injective (by rw [h, ofAdd_zsmul])

  have hqpos : 0 < q := hq
  have hkey : ∀ c d : ℤ, P ^ c * Q ^ d = 1 → (q : ℤ) ∣ c ∧ (q : ℤ) ∣ d := by
    intro c d hcd
    have hq0' : (0 : ℤ) < q := by exact_mod_cast hqpos
    set a : ℕ := (c % q).toNat with ha
    set b : ℕ := (d % q).toNat with hb
    have ha' : (a : ℤ) = c % q := Int.toNat_of_nonneg (Int.emod_nonneg _ hq0'.ne')
    have hb' : (b : ℤ) = d % q := Int.toNat_of_nonneg (Int.emod_nonneg _ hq0'.ne')
    have haq : a < q := by
      have := Int.emod_lt_of_pos c hq0'
      omega
    have hbq : b < q := by
      have := Int.emod_lt_of_pos d hq0'
      omega
    have hab : P ^ a * Q ^ b = 1 := by
      rw [← zpow_natCast, ← zpow_natCast, ha', hb', ← zpow_eq_zpow_emod' c hPq',
        ← zpow_eq_zpow_emod' d hQq']
      exact hcd
    have h00 : linComb GΩ P Q a b = linComb GΩ P Q 0 0 := by
      rw [hlin, hlin, hab, pow_zero, pow_zero, mul_one]
    obtain ⟨ha0, hb0⟩ := hinj a b 0 0 haq hbq hqpos hqpos h00
    refine ⟨Int.dvd_of_emod_eq_zero ?_, Int.dvd_of_emod_eq_zero ?_⟩
    · rw [← ha', ha0]; rfl
    · rw [← hb', hb0]; rfl

  refine ⟨?_, ?_⟩
  · rw [hΘx]
    refine ⟨?_, ?_, ?_⟩
    · show q • R P = 0
      rw [← natCast_zsmul, ← hR_zpow, zpow_natCast, hPq', hR_one']
    · show q • R Q = 0
      rw [← natCast_zsmul, ← hR_zpow, zpow_natCast, hQq', hR_one']
    · intro a b hab
      change a • R P + b • R Q = 0 at hab
      apply hkey
      apply hR_inj
      rw [hR_mul', hR_zpow, hR_zpow, hab, hR_one']

  intro σ
  set σA : Ω →ₐ[A] Ω := (σ : Ω →ₐ[K₀] Ω).restrictScalars A with hσA

  have hgf : (σ : Ω →+* Ω).comp (algebraMap K₀ Ω) = algebraMap K₀ Ω := RingHom.ext fun k => by
    show σ (algebraMap K₀ Ω k) = algebraMap K₀ Ω k
    exact σ.commutes k
  have hx' : WeierstrassCurve.map EΩ σA.toRingHom = EΩ := by
    show E.map ((σ : Ω →+* Ω).comp (algebraMap K₀ Ω)) = E.map (algebraMap K₀ Ω)
    rw [hgf]

  obtain ⟨hc, hpin⟩ := h𝒯.2 Ω Ω σA ⟨EΩ, P, Q⟩
  obtain ⟨φσ, hφσ, hcoefσ⟩ := hCO Ω Ω σA EΩ
  obtain ⟨hPpin, hQpin⟩ := hpin φσ hφσ hcoefσ
  have hy : (𝒯.map σA ⟨EΩ, P, Q⟩).curve = EΩ := hc.trans hx'
  rw [hΘ_pos _ hy, hΘx]

  have hcomp : eqToHom (congrArg projModelCR hx') ≫ Proj.map φ₀ hφ₀ = Proj.map φσ hφσ ≫ Proj.map φ₀ hφ₀ := by
    rw [← Proj.map_comp φ₀ φσ hφ₀ hφσ]
    symm
    exact projMap_eq_eqToHom_comp_projMap (E : WeierstrassCurve.Projective K₀) hgf
      (show projModelGradingCR (E : WeierstrassCurve.Projective K₀) →+*ᵍ
          projModelGradingCR ((E : WeierstrassCurve.Projective K₀).map
            ((σ : Ω →+* Ω).comp (algebraMap K₀ Ω))) from φσ.comp φ₀)
      (HomogeneousIdeal.irrelevant_le_map_comp hφ₀ hφσ)
      (isCoefficientHom_comp (E : WeierstrassCurve.Projective K₀) (algebraMap K₀ Ω) (σ : Ω →+* Ω)
        φ₀ hcoef₀' φσ hcoefσ)
      φ₀ hφ₀ hcoef₀' (congrArg projModelCR hx')

  have htw : ∀ (S : Section EΩ) (S' : Section ((𝒯.map σA ⟨EΩ, P, Q⟩).curve)),
      S'.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φσ hφσ =
        Spec.map (CommRingCat.ofHom σA.toRingHom) ≫ S.1 →
      push (castSec hy S') = galTwist σ (push S) := by
    intro S S' hS
    apply Subtype.ext
    rw [hpush_val, castSec_val]
    show (S'.1 ≫ eqToHom (congrArg projModelCR hy)) ≫ Proj.map φ₀ hφ₀ =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ (S.1 ≫ Proj.map φ₀ hφ₀)
    have htr : eqToHom (congrArg projModelCR hy) =
        eqToHom (congrArg projModelCR hc) ≫ eqToHom (congrArg projModelCR hx') := (eqToHom_trans _ _).symm
    calc (S'.1 ≫ eqToHom (congrArg projModelCR hy)) ≫ Proj.map φ₀ hφ₀
        = S'.1 ≫ eqToHom (congrArg projModelCR hc) ≫ (eqToHom (congrArg projModelCR hx') ≫ Proj.map φ₀ hφ₀) := by
          rw [htr]; simp only [Category.assoc]
      _ = (S'.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φσ hφσ) ≫ Proj.map φ₀ hφ₀ := by
          rw [hcomp]; simp only [Category.assoc]
      _ = (Spec.map (CommRingCat.ofHom σA.toRingHom) ≫ S.1) ≫ Proj.map φ₀ hφ₀ := by rw [hS]
      _ = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ (S.1 ≫ Proj.map φ₀ hφ₀) := by
          rw [Category.assoc]; rfl
  have hP' := htw P _ hPpin
  have hQ' := htw Q _ hQpin
  show (R (castSec hy (𝒯.map σA ⟨EΩ, P, Q⟩).P), R (castSec hy (𝒯.map σA ⟨EΩ, P, Q⟩).Q)) =
    (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (R P),
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (R Q))
  rw [hR_def, hR_def, hR_def, hR_def, hP', hQ', hR_gal, hR_gal]

end S_WeierstrassCurve_DrinfeldGlobal_exists_basisReading_levelComponent_map_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_basisReading_levelComponent_map_of_isAlgClosed (solution)

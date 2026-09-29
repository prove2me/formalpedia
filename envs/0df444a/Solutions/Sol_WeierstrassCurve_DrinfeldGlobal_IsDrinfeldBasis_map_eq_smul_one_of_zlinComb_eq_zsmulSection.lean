-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/184b3a7d-d1cb-5de1-9cb9-b2bf35f19387

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassProjModel_mul_comm_of_isPointsEval
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_map_eq_smul_one_of_zlinComb_eq_zsmulSection
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

namespace P2MKcDrinSign

universe u

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

end P2MKcDrinSign

open P2MKcDrinSign

set_option maxHeartbeats 3200000 in
theorem solution
    {K : Type} [Field K] (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ)
    (G : RelativeGroupLaw K (projModelStrCR W))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W) ≃ (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev)
    (q : ℕ) (hqK : (q : K) ≠ 0) (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hP : ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0) = ModularCurve.LevelRelabelling.zsmulSection G ε P)
    (hQ : ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1) = ModularCurve.LevelRelabelling.zsmulSection G ε Q) :
    g.map (Int.castRingHom (ZMod q)) = (ε : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  classical

  have hq0 : q ≠ 0 := by rintro rfl; exact hqK (by simp)
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  haveI hEll : WeierstrassCurve.IsElliptic W := ⟨hΔ⟩
  have hprop := WeierstrassProjModel.projModelStrCR_isProper W
  haveI : IsSeparated (projModelStrCR W) := inferInstance
  have hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (projModelStrCR W)), G.mul t x y = G.mul t y x :=
    fun t x y => WeierstrassProjModel.mul_comm_of_isPointsEval K W G ev hev t x y

  letI grp : CommGroup (Section W) :=
    { G.pointGroup (𝟙 _) with mul_comm := fun x y => hcomm (𝟙 _) x y }
  have hpow : ∀ (n : ℕ) (x : Section W), G.nsmul (𝟙 _) n x = x ^ n := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, ih, pow_succ]; rfl
  have hzpow : ∀ (n : ℤ) (x : Section W), ModularCurve.LevelRelabelling.zsmulSection G n x = x ^ n := by
    intro n x
    cases n with
    | ofNat k =>
      show G.nsmul (𝟙 _) k x = x ^ ((k : ℕ) : ℤ)
      rw [hpow, zpow_natCast]
    | negSucc k =>
      show G.inv (𝟙 _) (G.nsmul (𝟙 _) (k + 1) x) = x ^ (Int.negSucc k)
      rw [hpow, zpow_negSucc]
      rfl
  have hzlin : ∀ a b : ℤ, ModularCurve.LevelRelabelling.zlinComb G P Q a b = P ^ a * Q ^ b := by
    intro a b
    show G.mul (𝟙 _) (ModularCurve.LevelRelabelling.zsmulSection G a P)
      (ModularCurve.LevelRelabelling.zsmulSection G b Q) = P ^ a * Q ^ b
    rw [hzpow, hzpow]
    rfl
  have hlin : ∀ a b : ℕ, linComb G P Q a b = P ^ a * Q ^ b := by
    intro a b
    show G.mul (𝟙 _) (G.nsmul (𝟙 _) a P) (G.nsmul (𝟙 _) b Q) = P ^ a * Q ^ b
    rw [hpow, hpow]
    rfl

  have hP' : P ^ (g 0 0 + -ε) * Q ^ (g 1 0) = 1 := by
    rw [hzlin, hzpow] at hP
    have h := congrArg (fun z => z * P ^ (-ε)) hP
    beta_reduce at h
    rw [← zpow_add, add_neg_cancel, zpow_zero, mul_right_comm, ← zpow_add] at h
    exact h
  have hQ' : P ^ (g 0 1) * Q ^ (g 1 1 + -ε) = 1 := by
    rw [hzlin, hzpow] at hQ
    have h := congrArg (fun z => z * Q ^ (-ε)) hQ
    beta_reduce at h
    rw [← zpow_add, add_neg_cancel, zpow_zero, mul_assoc, ← zpow_add] at h
    exact h

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

  have hkfst_f : pullback.fst (G.schemeNsmul q) e ≫ projModelStrCR W = pullback.snd (G.schemeNsmul q) e := by
    calc pullback.fst (G.schemeNsmul q) e ≫ projModelStrCR W
          = pullback.fst (G.schemeNsmul q) e ≫ G.schemeNsmul q ≫ projModelStrCR W := by
            rw [G.schemeNsmul_over]
      _ = (pullback.fst (G.schemeNsmul q) e ≫ G.schemeNsmul q) ≫ projModelStrCR W :=
            (Category.assoc _ _ _).symm
      _ = (pullback.snd (G.schemeNsmul q) e ≫ e) ≫ projModelStrCR W := by rw [pullback.condition]
      _ = pullback.snd (G.schemeNsmul q) e := by rw [Category.assoc, he, Category.comp_id]
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

  let F : Type := AlgebraicClosure K
  have hqF : (q : F) ≠ 0 := by
    intro h0
    apply hqK
    apply (algebraMap K F).injective
    rw [map_natCast, h0, map_zero]
  set t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K F)) with ht_def

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
    let z : Spec (CommRingCat.of F) ⟶ pullback (G.schemeNsmul q) e := pullback.lift x.1 t hx'
    obtain ⟨i, hi⟩ := hA (z default)
    refine ⟨i, ?_⟩
    apply Subtype.ext
    symm
    show x.1 = t ≫ (sec i).1
    apply eq_comp_of_apply_eq (projModelStrCR W) (sec i).1 (sec i).2 x.1 x.2 default default
    rw [← hi, ← Scheme.Hom.comp_apply, pullback.lift_fst]

  let Pt : Type := (W.baseChange F).toAffine.Point
  let Φ : Fin (q * q) → Pt := fun i => ev F (bc (sec i))
  have hsurj : ∀ T : Pt, q • T = 0 → ∃ i, Φ i = T := by
    intro T hT
    have hx : G.nsmul t q ((ev F).symm T) = G.one t := by
      apply (ev F).injective
      rw [ev_nsmul W G ev hev, Equiv.apply_symm_apply, hT, ev_one W G ev hev]
    obtain ⟨i, hi⟩ := hB _ hx
    exact ⟨i, by simp only [Φ, hi, Equiv.apply_symm_apply]⟩
  have hcount : Nat.card ↥(Submodule.torsionBy ℤ Pt (q : ℤ)) = q ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := F) W hqF

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
      apply (ev F).injective
      rw [ev_nsmul W G ev hev, ev_one W G ev hev]
      exact h1
    rw [← hbc_nsmul, ← hbc_one] at h2
    have h3 := hbc_inj h2
    rw [hpow] at h3
    exact h3

  have hkey : ∀ c d : ℤ, P ^ c * Q ^ d = 1 → (q : ℤ) ∣ c ∧ (q : ℤ) ∣ d := by
    intro c d hcd
    rcases Nat.lt_or_ge q 2 with hq1 | hq2
    · have : q = 1 := by omega
      subst this
      simp

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
      rw [← zpow_natCast, ← zpow_natCast, ha', hb', ← zpow_eq_zpow_emod' c hPq,
        ← zpow_eq_zpow_emod' d hQq]
      exact hcd

    have hi_lt : a * q + b < q * q :=
      calc a * q + b < a * q + q := Nat.add_lt_add_left hbq _
        _ = (a + 1) * q := (Nat.succ_mul a q).symm
        _ ≤ q * q := Nat.mul_le_mul_right q haq
    have hi_div : (a * q + b) / q = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hqpos, Nat.div_eq_of_lt hbq, zero_add]
    have hi_mod : (a * q + b) % q = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbq]
    have h0lt : 0 < q * q := Nat.mul_pos hqpos hqpos
    have hseq : sec ⟨a * q + b, hi_lt⟩ = sec ⟨0, h0lt⟩ := by
      show linComb G P Q ((a * q + b) / q) ((a * q + b) % q) = linComb G P Q (0 / q) (0 % q)
      rw [hi_div, hi_mod, Nat.zero_div, Nat.zero_mod, hlin, hlin, hab, pow_zero, pow_zero, mul_one]
    have hidx : a * q + b = 0 := congrArg Fin.val (hsec_inj hseq)
    have ha0 : a = 0 := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exact h
      · exfalso
        have : q ≤ a * q + b := le_add_right (Nat.le_mul_of_pos_left q h)
        omega
    have hb0 : b = 0 := by omega
    refine ⟨Int.dvd_of_emod_eq_zero ?_, Int.dvd_of_emod_eq_zero ?_⟩
    · rw [← ha', ha0]; rfl
    · rw [← hb', hb0]; rfl

  obtain ⟨h00, h10⟩ := hkey _ _ hP'
  obtain ⟨h01, h11⟩ := hkey _ _ hQ'
  have e00 : ((g 0 0 : ℤ) : ZMod q) = (ε : ZMod q) := by
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_add_neg]
    exact h00
  have e11 : ((g 1 1 : ℤ) : ZMod q) = (ε : ZMod q) := by
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_add_neg]
    exact h11
  have e10 : ((g 1 0 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h10
  have e01 : ((g 0 1 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h01
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.map_apply, Matrix.smul_apply] using e00
  · simpa [Matrix.map_apply, Matrix.smul_apply] using e01
  · simpa [Matrix.map_apply, Matrix.smul_apply] using e10
  · simpa [Matrix.map_apply, Matrix.smul_apply] using e11

end S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_map_eq_smul_one_of_zlinComb_eq_zsmulSection
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_map_eq_smul_one_of_zlinComb_eq_zsmulSection (solution)

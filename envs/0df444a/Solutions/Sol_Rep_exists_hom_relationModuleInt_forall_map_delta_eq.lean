-- Prove2me | solution 1 for Rep.exists_hom_relationModuleInt_forall_map_delta_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8a31c17e-64e7-53bb-8248-682d5a69cfc9

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Theorems.Thm_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq_of_shortExact
import Theorems.Thm_Rep_IsTateCupProduct_cup_mk_right_eq_tateMap
import Theorems.Thm_Rep_exists_isTateCupProduct
import Theorems.Thm_Rep_isZero_tateCohomology_res_free
import Theorems.Thm_groupCohomology_bijective_map_top_subtype
import Theorems.Thm_groupCohomology_map_delta_eq_delta_map
import Theorems.Thm_Rep_moduleFree_relationCarrier
import Theorems.Thm_Rep_moduleFinite_relationCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_hom_relationModuleInt_forall_map_delta_eq
p2m_attr_erase "simp" "Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_dimShiftDownObjMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

namespace SurjCard

namespace Gen

universe u
variable {k G : Type u} [CommRing k] [Group G]

private theorem shortExact_map_resFunctor (S : Subgroup G) {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    (X.map (Rep.resFunctor S.subtype)).ShortExact := by
  have hex : ∀ y : X.X₂, X.g.hom y = 0 → ∃ x : X.X₁, X.f.hom x = y := by
    intro y hy
    have h' := hX.exact.map (forget₂ (Rep.{u} k G) (ModuleCat k))
    rw [ShortComplex.moduleCat_exact_iff] at h'
    obtain ⟨x, hx⟩ := h' y (by first | exact hy | simpa using hy)
    exact ⟨x, by first | exact hx | simpa using hx⟩
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · refine (forget₂ (Rep.{u} k S) (ModuleCat k)).reflects_exact_of_faithful _ ?_
    refine (ShortComplex.moduleCat_exact_iff _).2 fun y hy => ?_
    obtain ⟨x, hx⟩ := hex y (by first | exact hy | simpa using hy)
    exact ⟨x, by first | exact hx | simpa using hx⟩
  · exact (Rep.mono_iff_injective _).2 ((Rep.mono_iff_injective X.f).1 hX.mono_f)
  · exact (Rep.epi_iff_surjective _).2 ((Rep.epi_iff_surjective X.g).1 hX.epi_g)

private noncomputable def tmulRight (A M : Rep.{u} k G) (b : M.ρ.invariants) : A ⟶ A ⊗ M :=
  Rep.ofHom ⟨(TensorProduct.mk k A M).flip (b : M), fun g => by
    refine LinearMap.ext fun a => ?_
    change (A.ρ g a) ⊗ₜ[k] (b : M) = (A ⊗ M).ρ g (a ⊗ₜ[k] (b : M))
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul]
    congr 1
    exact (b.2 g).symm⟩

private theorem tmulRight_hom_apply (A M : Rep.{u} k G) (b : M.ρ.invariants) (a : A) :
    (tmulRight A M b).hom a = a ⊗ₜ[k] (b : M) := rfl

private theorem tmulRight_comp_ev (A C : Rep.{u} k G) (f : A ⟶ C) :
    tmulRight A ((ihom A).obj C) ((Representation.linHom.invariantsEquivRepHom A C).symm f) ≫ (ihom.ev A).app C = f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext fun a => ?_
  change ((ihom.ev A).app C).hom.toLinearMap (a ⊗ₜ[k] (f.hom.toLinearMap : A →ₗ[k] C)) = f.hom a
  rw [Rep.ihom_ev_app_hom]
  rfl

private theorem norm_linHom_apply [Fintype G] (A C : Rep.{u} k G) (χ : A →ₗ[k] C) (x : A) :
    (Representation.linHom A.ρ C.ρ).norm χ x = ∑ g : G, C.ρ g (χ (A.ρ g⁻¹ x)) := by
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, Representation.linHom_apply,
    LinearMap.comp_apply]

private noncomputable def cls [Fintype G] (M : Rep.{u} k G) (b : M.ρ.invariants) : M.tateH0 := Submodule.Quotient.mk b

private theorem cls_def [Fintype G] (M : Rep.{u} k G) (b : M.ρ.invariants) : cls M b = (SurjCard.Gen.cls M b) := rfl

private theorem cls_eq_zero_iff [Fintype G] (M : Rep.{u} k G) (b : M.ρ.invariants) :
    cls M b = 0 ↔ ∃ χ : M, M.ρ.norm χ = (b : M) := by
  change (Submodule.Quotient.mk b : M.tateH0) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨χ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    refine ⟨χ, ?_⟩
    have := congrArg Subtype.val hc
    change (M.ρ.normBar (Representation.Coinvariants.mk M.ρ χ) : M) = b at this
    rwa [Representation.normBar_mk, Representation.coe_normToInvariants_apply] at this
  · rintro ⟨χ, hχ⟩
    refine ⟨Representation.Coinvariants.mk M.ρ χ, Subtype.ext ?_⟩
    rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply, hχ]

private theorem cup_cls_right_eq_tateMap [Fintype G] {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup)
    (A M : Rep.{u} k G) (b : M.ρ.invariants) (p : ℤ) (x : A.tateCohomology p) :
    cup A M p 0 p (add_zero p) x (cls M b) = (Rep.tateMap (tmulRight A M b) p).hom x :=
  hcup.cup_mk_right_eq_tateMap A M b _ (tmulRight_hom_apply A M b) p x

private theorem tmulRight_comp_ev' (A C : Rep.{u} k G) (b : ((ihom A).obj C).ρ.invariants) :
    tmulRight A ((ihom A).obj C) b ≫ (ihom.ev A).app C = Representation.linHom.invariantsEquivRepHom A C b := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext fun a => ?_
  change ((ihom.ev A).app C).hom.toLinearMap (a ⊗ₜ[k] b.1) = (show A →ₗ[k] C from b.1) a
  rw [Rep.ihom_ev_app_hom]
  rfl

private theorem exists_cls_eq [Fintype G] (M : Rep.{u} k G) (a : M.tateH0) : ∃ b : M.ρ.invariants, cls M b = a :=
  Submodule.Quotient.mk_surjective _ a

private def liftTop (A C : Rep.{u} k G) (f : Rep.res (⊤ : Subgroup G).subtype A ⟶ Rep.res (⊤ : Subgroup G).subtype C) :
    A ⟶ C :=
  Rep.ofHom ⟨f.hom.toLinearMap, fun g => f.hom.2 ⟨g, Subgroup.mem_top g⟩⟩

private theorem resFunctor_map_liftTop (A C : Rep.{u} k G)
    (f : Rep.res (⊤ : Subgroup G).subtype A ⟶ Rep.res (⊤ : Subgroup G).subtype C) :
    (Rep.resFunctor (⊤ : Subgroup G).subtype).map (liftTop A C f) = f := rfl

private theorem norm_linHom_res_top_apply [Fintype G] [Fintype (⊤ : Subgroup G)] (A C : Rep.{u} k G) (χ : A →ₗ[k] C) (x : A) :
    (Representation.linHom (Rep.res (⊤ : Subgroup G).subtype A).ρ (Rep.res (⊤ : Subgroup G).subtype C).ρ).norm χ x =
      ∑ g : G, C.ρ g (χ (A.ρ g⁻¹ x)) := by
  classical
  rw [norm_linHom_apply]
  exact Fintype.sum_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv _ _ fun s => rfl

private theorem exists_sum_eq_of_cls_eq_zero [Fintype G] [Fintype (⊤ : Subgroup G)] (A C : Rep.{u} k G)
    (f : Rep.res (⊤ : Subgroup G).subtype A ⟶ Rep.res (⊤ : Subgroup G).subtype C)
    (h : cls ((ihom (Rep.res (⊤ : Subgroup G).subtype A)).obj (Rep.res (⊤ : Subgroup G).subtype C))
      ((Representation.linHom.invariantsEquivRepHom _ _).symm f) = 0) :
    ∃ χ : A →ₗ[k] C, ∀ x : A, f.hom x = ∑ g : G, C.ρ g (χ (A.ρ g⁻¹ x)) := by
  classical
  obtain ⟨χ, hχ⟩ := (cls_eq_zero_iff _ _).1 h
  refine ⟨χ, fun x => ?_⟩
  have hx := LinearMap.congr_fun hχ x
  rw [← norm_linHom_res_top_apply]
  exact hx.symm

private theorem cls_eq_zero_of_forall_eq_sum [Fintype G] [Fintype (⊤ : Subgroup G)] (A C : Rep.{u} k G)
    (f : Rep.res (⊤ : Subgroup G).subtype A ⟶ Rep.res (⊤ : Subgroup G).subtype C) (χ : A →ₗ[k] C)
    (h : ∀ x : A, f.hom x = ∑ g : G, C.ρ g (χ (A.ρ g⁻¹ x))) :
    cls ((ihom (Rep.res (⊤ : Subgroup G).subtype A)).obj (Rep.res (⊤ : Subgroup G).subtype C))
      ((Representation.linHom.invariantsEquivRepHom _ _).symm f) = 0 := by
  classical
  refine (cls_eq_zero_iff _ _).2 ⟨χ, LinearMap.ext fun x => ?_⟩
  exact (norm_linHom_res_top_apply A C χ x).trans (h x).symm

end Gen

private def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

end SurjCard

open SurjCard in
theorem solution {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (B : Rep ℤ G) [Fintype B] (hX : (Rep.relationSeqInt B).ShortExact)
    (θ : groupCohomology B 1 →+ groupCohomology C 2) :
    ∃ φ : Rep.relationModuleInt B ⟶ C, ∀ y : groupCohomology B 1,
      (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) = θ y := by
  classical

  let S : Subgroup G := ⊤
  let i : S →* G := S.subtype
  obtain ⟨cup, hcup⟩ := Rep.exists_isTateCupProduct (k := ℤ) (G := ↥S)
  let R : Rep ℤ G := Rep.relationModuleInt B
  let Rr : Rep ℤ S := Rep.res i (Rep.of (Rep.relationRepInt B))
  let Cr : Rep ℤ S := Rep.res i C
  let Br : Rep ℤ S := Rep.res i B
  let M : Rep ℤ S := (ihom Rr).obj Cr
  have hXr : ((ShortComplex.mk (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (Rep.relationModuleInt_ι_comp_freeCover B)).map (Rep.resFunctor i)).ShortExact :=
    SurjCard.Gen.shortExact_map_resFunctor S hX
  haveI : Module.Free ℤ (Rep.relationCarrier B) := Rep.moduleFree_relationCarrier B
  haveI : Module.Finite ℤ (Rep.relationCarrier B) := Rep.moduleFinite_relationCarrier B

  have hmap_comp : ∀ {H : Type} [Group H] {X Y Z : Rep ℤ H} (a : X ⟶ Y) (c : Y ⟶ Z) (n : ℕ) (x : groupCohomology X n),
      (groupCohomology.map (MonoidHom.id H) (a ≫ c) n).hom x =
        (groupCohomology.map (MonoidHom.id H) c n).hom ((groupCohomology.map (MonoidHom.id H) a n).hom x) := by
    intro H _ X Y Z a c n x
    rw [groupCohomology.map_id_comp, ModuleCat.comp_apply]

  have hres1 : Function.Bijective (groupCohomology.map i (𝟙 Br) 1).hom := groupCohomology.bijective_map_top_subtype B 1
  have hres2 : Function.Injective (groupCohomology.map i (𝟙 Cr) 2).hom :=
    (groupCohomology.bijective_map_top_subtype C 2).1
  have hδnat : ∀ y : groupCohomology B 1,
      (groupCohomology.map i (𝟙 Rr) 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) =
        (groupCohomology.δ hXr 1 2 rfl).hom ((groupCohomology.map i (𝟙 Br) 1).hom y) :=
    fun y => groupCohomology.map_delta_eq_delta_map i hX hXr (𝟙 _) (𝟙 _) (𝟙 _)
      (by erw [Category.comp_id]; try erw [Category.id_comp]) (by erw [Category.comp_id]; try erw [Category.id_comp]) 1 2 rfl y
  have hmapnat : ∀ (φ : R ⟶ C) (w : groupCohomology R 2),
      (groupCohomology.map (MonoidHom.id S) ((Rep.resFunctor i).map φ) 2).hom ((groupCohomology.map i (𝟙 Rr) 2).hom w) =
        (groupCohomology.map i (𝟙 Cr) 2).hom ((groupCohomology.map (MonoidHom.id G) φ 2).hom w) := by
    intro φ w
    have h := (groupCohomology.resNatTrans ℤ i 2).naturality φ
    have h' := congrArg (fun f => (ModuleCat.Hom.hom f) w) h
    simp only [Functor.comp_map, groupCohomology.functor_map, groupCohomology.resNatTrans_app] at h'
    exact h'.symm

  let e1 : groupCohomology B 1 ≃ₗ[ℤ] groupCohomology Br 1 :=
    LinearEquiv.ofBijective (groupCohomology.map i (𝟙 Br) 1).hom hres1
  let θℓ : groupCohomology B 1 →ₗ[ℤ] groupCohomology C 2 := SurjCard.toIntLinearMapOfModules _ _ θ
  let θ' : groupCohomology Br 1 →ₗ[ℤ] groupCohomology Cr 2 :=
    (groupCohomology.map i (𝟙 Cr) 2).hom ∘ₗ θℓ ∘ₗ e1.symm.toLinearMap
  have hθ' : ∀ y : groupCohomology B 1,
      θ' ((groupCohomology.map i (𝟙 Br) 1).hom y) = (groupCohomology.map i (𝟙 Cr) 2).hom (θ y) := by
    intro y
    change (groupCohomology.map i (𝟙 Cr) 2).hom (θ (e1.symm (e1 y))) = _
    rw [LinearEquiv.symm_apply_apply]

  obtain ⟨a, ha⟩ := Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq_of_shortExact C u h1 h2card h2gen
    (Rep.relationCarrier B) (Rep.relationRepInt B) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
    (Rep.relationModuleInt_ι_comp_freeCover B) S cup hcup hXr (Rep.isZero_tateCohomology_res_free S B) 1 0 (by norm_num) θ'
  obtain ⟨b, hb⟩ := SurjCard.Gen.exists_cls_eq M a
  let φr : Rr ⟶ Cr := Representation.linHom.invariantsEquivRepHom Rr Cr b
  let φ : R ⟶ C := SurjCard.Gen.liftTop (Rep.of (Rep.relationRepInt B)) C φr
  have hφr : (Rep.resFunctor i).map φ = φr := SurjCard.Gen.resFunctor_map_liftTop _ _ φr
  let ψ : Rr ⟶ Rr ⊗ M := SurjCard.Gen.tmulRight Rr M b
  have hψev : ψ ≫ (ihom.ev Rr).app Cr = φr := SurjCard.Gen.tmulRight_comp_ev' Rr Cr b
  have hpair : ∀ z : Rr.tateCohomology 2,
      (Rep.tateMap ((ihom.ev Rr).app Cr) 2).hom (cup Rr M 2 0 2 (add_zero 2) z (SurjCard.Gen.cls M b)) =
        (groupCohomology.map (MonoidHom.id S) φr 2).hom z := by
    intro z
    rw [SurjCard.Gen.cup_cls_right_eq_tateMap hcup Rr M b 2 z]
    change (groupCohomology.map (MonoidHom.id S) ((ihom.ev Rr).app Cr) 2).hom
      ((groupCohomology.map (MonoidHom.id S) ψ 2).hom z) = _
    rw [← hmap_comp, hψev]

  refine ⟨φ, fun y => hres2 ?_⟩
  rw [← hmapnat, hφr, hδnat, ← hpair, hb, ← hθ']
  exact ha _

end S_Rep_exists_hom_relationModuleInt_forall_map_delta_eq
end P2MW
export P2MW.S_Rep_exists_hom_relationModuleInt_forall_map_delta_eq (solution)

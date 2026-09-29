-- Prove2me | solution 1 for Rep.exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/46a791de-fc9a-5b0b-9eeb-b65196985146

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Theorems.Thm_Rep_forall_map_delta_eq_zero_iff_exists_eq_sum_rho
import Theorems.Thm_Rep_moduleFree_relationCarrier
import Theorems.Thm_Rep_relationSeqInt_shortExact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective
p2m_attr_erase "simp" "Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_dimShiftDownObjMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
open CategoryTheory CategoryTheory.Limits

namespace KerStep

namespace Gen

universe u
variable {k : Type u} [CommRing k] {G : Type u} [Group G]

def homOfLinear {V W : Rep.{u} k G} (L : V →ₗ[k] W) (h : ∀ (g : G) (x : V), L (V.ρ g x) = W.ρ g (L x)) : V ⟶ W :=
  Rep.ofHom ⟨L, fun g => LinearMap.ext (h g)⟩

@[scoped simp] lemma homOfLinear_hom_apply {V W : Rep.{u} k G} (L : V →ₗ[k] W) (h : ∀ (g : G) (x : V), L (V.ρ g x) = W.ρ g (L x)) (x : V) :
    (homOfLinear L h).hom x = L x := rfl

private def _root_.KerStep.Gen.addHom {V W : Rep.{u} k G} (a : V ⟶ W) : V →+ W := a.hom.toLinearMap.toAddMonoidHom
p2m_export "KerStep.Gen" "addHom"
@[scoped simp] private lemma _root_.KerStep.Gen.addHom_apply {V W : Rep.{u} k G} (a : V ⟶ W) (x : V) : addHom a x = a.hom x := rfl

p2m_export "KerStep.Gen" "addHom_apply"

def ρAdd (V : Rep.{u} k G) (g : G) : V →+ V := (V.ρ g).toAddMonoidHom
@[scoped simp] lemma ρAdd_apply (V : Rep.{u} k G) (g : G) (x : V) : ρAdd V g x = V.ρ g x := rfl

lemma ρ_mul_apply (V : Rep.{u} k G) (g h : G) (x : V) : V.ρ (g * h) x = V.ρ g (V.ρ h x) := by
  rw [map_mul, Module.End.mul_apply]

def normAdd [Fintype G] (V W : Rep.{u} k G) (κ : V →+ W) : V →+ W :=
  ∑ g : G, (ρAdd W g).comp (κ.comp (ρAdd V g⁻¹))

lemma normAdd_apply [Fintype G] (V W : Rep.{u} k G) (κ : V →+ W) (x : V) :
    normAdd V W κ x = ∑ g : G, W.ρ g (κ (V.ρ g⁻¹ x)) := by
  simp [normAdd]

lemma normAdd_equivariant [Fintype G] (V W : Rep.{u} k G) (κ : V →+ W) (h : G) (x : V) :
    normAdd V W κ (V.ρ h x) = W.ρ h (normAdd V W κ x) := by
  rw [normAdd_apply, normAdd_apply]
  change _ = ρAdd W h (∑ g : G, W.ρ g (κ (V.ρ g⁻¹ x)))
  rw [map_sum]
  simp only [ρAdd_apply]

  rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  simp only [Equiv.coe_mulLeft, mul_inv_rev, ρ_mul_apply]
  rw [← ρ_mul_apply V h⁻¹ h, inv_mul_cancel, map_one, Module.End.one_apply]

end Gen
p2m_reactivate "P2MW.S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective.KerStep.Gen"

open Gen

def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

def homOfAddMonoidHom {G : Type} [Group G] (X C : Rep.{0} ℤ G) (φ : X →+ C)
    (hφ : ∀ (g : G) (x : X), φ (X.ρ g x) = C.ρ g (φ x)) : X ⟶ C :=
  homOfLinear (toIntLinearMapOfModules _ _ φ) hφ

theorem homOfAddMonoidHom_hom_apply {G : Type} [Group G] (X C : Rep.{0} ℤ G) (φ : X →+ C)
    (hφ : ∀ (g : G) (x : X), φ (X.ρ g x) = C.ρ g (φ x)) (x : X) : (homOfAddMonoidHom X C φ hφ).hom x = φ x := rfl

private def _root_.KerStep.normAdd {G : Type} [Group G] [Fintype G] (X C : Rep.{0} ℤ G) (k : X →+ C) : X →+ C := Gen.normAdd X C k

p2m_export "KerStep" "normAdd"
private theorem _root_.KerStep.normAdd_apply {G : Type} [Group G] [Fintype G] (X C : Rep.{0} ℤ G) (k : X →+ C) (x : X) :
    normAdd X C k x = ∑ g : G, C.ρ g (k (X.ρ g⁻¹ x)) := Gen.normAdd_apply X C k x

p2m_export "KerStep" "normAdd_apply"
private theorem _root_.KerStep.normAdd_equivariant {G : Type} [Group G] [Fintype G] (X C : Rep.{0} ℤ G) (k : X →+ C) (h : G) (x : X) :
    normAdd X C k (X.ρ h x) = C.ρ h (normAdd X C k x) := Gen.normAdd_equivariant X C k h x

p2m_export "KerStep" "normAdd_equivariant"

def norm {G : Type} [Group G] [Fintype G] (X C : Rep.{0} ℤ G) (k : X →+ C) : X ⟶ C :=
  homOfAddMonoidHom X C (normAdd X C k) (normAdd_equivariant X C k)

theorem norm_hom_apply {G : Type} [Group G] [Fintype G] (X C : Rep.{0} ℤ G) (k : X →+ C) (x : X) :
    (norm X C k).hom x = ∑ g : G, C.ρ g (k (X.ρ g⁻¹ x)) := normAdd_apply X C k x

private def _root_.KerStep.addHom {G : Type} [Group G] {X Y : Rep.{0} ℤ G} (a : X ⟶ Y) : X →+ Y := Gen.addHom a

p2m_export "KerStep" "addHom"
private theorem _root_.KerStep.addHom_apply {G : Type} [Group G] {X Y : Rep.{0} ℤ G} (a : X ⟶ Y) (x : X) : addHom a x = a.hom x := rfl

p2m_export "KerStep" "addHom_apply"

theorem comp_norm {G : Type} [Group G] [Fintype G] {X' X C : Rep.{0} ℤ G} (a : X' ⟶ X) (k : X →+ C) :
    a ≫ norm X C k = norm X' C (k.comp (addHom a)) := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro x
  change (norm X C k).hom (a.hom x) = (norm X' C (k.comp (addHom a))).hom x
  rw [norm_hom_apply, norm_hom_apply]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [AddMonoidHom.comp_apply, addHom_apply, Rep.hom_comm_apply]

theorem norm_comp {G : Type} [Group G] [Fintype G] {X C C' : Rep.{0} ℤ G} (k : X →+ C) (c : C ⟶ C') :
    norm X C k ≫ c = norm X C' ((addHom c).comp k) := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro x
  change c.hom ((norm X C k).hom x) = (norm X C' ((addHom c).comp k)).hom x
  rw [norm_hom_apply, norm_hom_apply]
  change Gen.addHom c _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Gen.addHom_apply, AddMonoidHom.comp_apply, addHom_apply, Rep.hom_comm_apply]

end KerStep
p2m_reactivate "P2MW.S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective.KerStep.Gen P2MW.S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective.KerStep"

universe u

namespace Rep p2m_export "Rep" "hom_comm_apply V free desc subtype ofHom of Hom.hom norm res epi_iff_surjective mono_iff_injective ρ comp_apply hV2 add_hom Hom hom_ext freeCover relationCarrier relationRepInt relationModuleInt relationModuleInt.ι relationModuleInt_ι_comp_freeCover relationSeqInt forall_map_delta_eq_zero_iff_exists_eq_sum_rho moduleFree_relationCarrier relationSeqInt_shortExact" end Rep
p2m_open_scoped "Rep" in
theorem Rep.exists_hom_eq_of_exact_mk {k G : Type u} [CommRing k] [Group G] {X Y Z : Rep.{u} k G}
    (a : X ⟶ Y) (b : Y ⟶ Z) (w : a ≫ b = 0)
    (h : (ShortComplex.mk a b w).Exact) (y : Y) (hy : b.hom y = 0) : ∃ x : X, a.hom x = y := by
  have h' := h.map (forget₂ (Rep.{u} k G) (ModuleCat k))
  rw [ShortComplex.moduleCat_exact_iff] at h'
  obtain ⟨x, hx⟩ := h' y (by (first | exact hy | simpa using hy | (have h__ := hy; simp at h__; exact h__)))
  exact ⟨x, by (first | exact hx | simpa using hx | (have h__ := hx; simp at h__; exact h__))⟩

namespace KerStep

theorem exists_comparison {G : Type} [Group G]
    {R P X R' P' X' : Rep.{0} ℤ G} (f : R ⟶ P) (g : P ⟶ X) (f' : R' ⟶ P') (g' : P' ⟶ X') (w' : f' ≫ g' = 0)
    (hT' : (ShortComplex.mk f' g' w').ShortExact)
    (hP : ∀ (A Y : Rep.{0} ℤ G) (e : A ⟶ Y), Function.Surjective e.hom → ∀ χ : P ⟶ Y, ∃ χ' : P ⟶ A, χ' ≫ e = χ)
    (w : f ≫ g = 0) (m : X ⟶ X') :
    ∃ (cR : R ⟶ R') (cP : P ⟶ P'), f ≫ cP = cR ≫ f' ∧ g ≫ m = cP ≫ g' := by
  obtain ⟨cP, hcP⟩ := hP _ _ g' ((Rep.epi_iff_surjective g').1 hT'.epi_g) (g ≫ m)
  haveI : Mono f' := hT'.mono_f
  have h0 : (f ≫ cP) ≫ (ShortComplex.mk f' g' w').g = 0 := by
    change (f ≫ cP) ≫ g' = 0
    rw [Category.assoc, hcP, ← Category.assoc, w, zero_comp]
  exact ⟨hT'.exact.lift (f ≫ cP) h0, cP, (hT'.exact.lift_f _ _).symm, hcP.symm⟩

theorem exists_sub_eq_comp {G : Type} [Group G]
    {R P X R' P' X' : Rep.{0} ℤ G} (f : R ⟶ P) (g : P ⟶ X) (f' : R' ⟶ P') (g' : P' ⟶ X') (w' : f' ≫ g' = 0)
    (hT' : (ShortComplex.mk f' g' w').ShortExact) (m : X ⟶ X')
    (cR dR : R ⟶ R') (cP dP : P ⟶ P')
    (hc₁ : f ≫ cP = cR ≫ f') (hc₂ : g ≫ m = cP ≫ g') (hd₁ : f ≫ dP = dR ≫ f') (hd₂ : g ≫ m = dP ≫ g') :
    ∃ t : P ⟶ R', cR - dR = f ≫ t := by
  haveI : Mono f' := hT'.mono_f
  have h0 : (cP - dP) ≫ (ShortComplex.mk f' g' w').g = 0 := by
    change (cP - dP) ≫ g' = 0
    rw [Preadditive.sub_comp, ← hc₂, ← hd₂, sub_self]
  refine ⟨hT'.exact.lift (cP - dP) h0, ?_⟩
  rw [← cancel_mono f', Category.assoc, hT'.exact.lift_f, Preadditive.comp_sub, Preadditive.sub_comp, hc₁, hd₁]

theorem exists_retraction {G : Type} [Group G] {X Y : Rep.{0} ℤ G} {V : Type} [AddCommGroup V] [Module.Projective ℤ V]
    (τ : Representation ℤ G V) (j : X ⟶ Y) (q : Y ⟶ Rep.of τ) (w : j ≫ q = 0)
    (h : (ShortComplex.mk j q w).ShortExact) :
    ∃ r : Y →+ X, ∀ x : X, r (j.hom x) = x := by
  have hq : Function.Surjective q.hom := (Rep.epi_iff_surjective q).1 h.epi_g
  have hj : Function.Injective j.hom := (Rep.mono_iff_injective j).1 h.mono_f
  letI := Y.hV2
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (q.hom.toLinearMap) (LinearMap.id) hq
  have hs' : ∀ v : V, q.hom (s v) = v := fun v => LinearMap.congr_fun hs v
  have hex : ∀ y : Y, q.hom y = 0 → ∃ x : X, j.hom x = y :=
    fun y hy => Rep.exists_hom_eq_of_exact_mk j q w h.exact y hy

  have hmem : ∀ y : Y, ∃ x : X, j.hom x = y - s (q.hom y) := by
    intro y
    apply hex
    rw [map_sub, hs', sub_self]
  refine ⟨{ toFun := fun y => Classical.choose (hmem y)
            map_zero' := hj (by
              rw [Classical.choose_spec (hmem 0)]
              simp)
            map_add' := fun y y' => hj (by
              rw [map_add j.hom, Classical.choose_spec (hmem (y + y')), Classical.choose_spec (hmem y),
                Classical.choose_spec (hmem y'), map_add q.hom y y', map_add s]
              abel) }, fun x => hj ?_⟩
  change j.hom (Classical.choose (hmem (j.hom x))) = j.hom x
  rw [Classical.choose_spec (hmem _)]
  have : q.hom (j.hom x) = 0 := by
    change (j ≫ q).hom x = 0
    rw [w]
    rfl
  rw [this, map_zero, sub_zero]

end KerStep
p2m_reactivate "P2MW.S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective.KerStep.Gen P2MW.S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective.KerStep"

p2m_open_scoped "Rep" in

theorem Rep.exact_mk_of_forall_exists_hom_eq {k G : Type u} [CommRing k] [Group G] {X Y Z : Rep.{u} k G}
    (a : X ⟶ Y) (b : Y ⟶ Z) (w : a ≫ b = 0)
    (h : ∀ y : Y, b.hom y = 0 → ∃ x : X, a.hom x = y) : (ShortComplex.mk a b w).Exact := by
  refine (forget₂ (Rep.{u} k G) (ModuleCat k)).reflects_exact_of_faithful _ ?_
  refine (ShortComplex.moduleCat_exact_iff _).2 fun y hy => ?_
  obtain ⟨x, hx⟩ := h y (by (first | exact hy | simpa using hy | (have h__ := hy; simp at h__; exact h__)))
  exact ⟨x, by (first | exact hx | simpa using hx | (have h__ := hx; simp at h__; exact h__))⟩

theorem KerStep.horseshoe
    {G : Type} [Group G]
    {SB : ShortComplex (Rep.{0} ℤ G)} (hSB : SB.ShortExact)
    {R_B P_B : Rep.{0} ℤ G} (f_B : R_B ⟶ P_B) (g_B : P_B ⟶ SB.X₁) (w_B : f_B ≫ g_B = 0)
    (hT_B : (ShortComplex.mk f_B g_B w_B).ShortExact)
    {R₁ P₁ : Rep.{0} ℤ G} (f₁ : R₁ ⟶ P₁) (g₁ : P₁ ⟶ SB.X₃) (w₁ : f₁ ≫ g₁ = 0)
    (hT₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact)
    (hP₁ : ∀ (X Y : Rep.{0} ℤ G) (e : X ⟶ Y), Function.Surjective e.hom → ∀ χ : P₁ ⟶ Y, ∃ χ' : P₁ ⟶ X, χ' ≫ e = χ) :
    ∃ (R : Rep.{0} ℤ G) (f : R ⟶ P_B ⊞ P₁) (g : P_B ⊞ P₁ ⟶ SB.X₂) (w : f ≫ g = 0)
      (_ : (ShortComplex.mk f g w).ShortExact)
      (j : R_B ⟶ R) (q : R ⟶ R₁) (wR : j ≫ q = 0) (_ : (ShortComplex.mk j q wR).ShortExact),
      f_B ≫ biprod.inl = j ≫ f ∧ g_B ≫ SB.f = biprod.inl ≫ g ∧ f ≫ biprod.snd = q ≫ f₁ ∧ g ≫ SB.g = biprod.snd ≫ g₁ := by
  classical

  have capp : ∀ {X Y Z : Rep.{0} ℤ G} (a : X ⟶ Y) (b : Y ⟶ Z) (x : X), (a ≫ b).hom x = b.hom (a.hom x) :=
    fun a b x => rfl
  have hex : ∀ {X Y Z : Rep.{0} ℤ G} (a : X ⟶ Y) (b : Y ⟶ Z) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).Exact → ∀ y : Y, b.hom y = 0 → ∃ x : X, a.hom x = y :=
    fun a b w h y hy => Rep.exists_hom_eq_of_exact_mk a b w h y hy
  have hsurj : ∀ {X Y : Rep.{0} ℤ G} (e : X ⟶ Y), Epi e → Function.Surjective e.hom :=
    fun e he => (Rep.epi_iff_surjective e).1 he
  have hinj : ∀ {X Y : Rep.{0} ℤ G} (e : X ⟶ Y), Mono e → Function.Injective e.hom :=
    fun e he => (Rep.mono_iff_injective e).1 he

  obtain ⟨lam, hlam⟩ := hP₁ _ _ SB.g (hsurj SB.g hSB.epi_g) g₁
  let g : P_B ⊞ P₁ ⟶ SB.X₂ := biprod.desc (g_B ≫ SB.f) lam
  have hinl_g : biprod.inl ≫ g = g_B ≫ SB.f := biprod.inl_desc _ _
  have hinr_g : biprod.inr ≫ g = lam := biprod.inr_desc _ _
  have hgρ : g ≫ SB.g = biprod.snd ≫ g₁ := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, hinl_g, Category.assoc, SB.zero, comp_zero, ← Category.assoc, biprod.inl_snd, zero_comp]
    · rw [← Category.assoc, hinr_g, hlam, ← Category.assoc, biprod.inr_snd, Category.id_comp]

  let f : kernel g ⟶ P_B ⊞ P₁ := kernel.ι g
  have w : f ≫ g = 0 := kernel.condition g
  have hg_surj : Function.Surjective g.hom := by
    intro i
    obtain ⟨p₁, hp₁⟩ := hsurj g₁ hT₁.epi_g (SB.g.hom i)
    have h0 : SB.g.hom (i - lam.hom p₁) = 0 := by
      rw [map_sub, ← capp lam SB.g, hlam, hp₁, sub_self]
    obtain ⟨b, hb⟩ := hex SB.f SB.g SB.zero hSB.exact _ h0
    obtain ⟨p, hp⟩ := hsurj g_B hT_B.epi_g b
    refine ⟨(biprod.inl : P_B ⟶ P_B ⊞ P₁).hom p + (biprod.inr : P₁ ⟶ P_B ⊞ P₁).hom p₁, ?_⟩
    rw [map_add, ← capp, ← capp, hinl_g, hinr_g, capp, hp, hb, sub_add_cancel]
  have hTg : (ShortComplex.mk f g w).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel g)
      mono_f := by dsimp; infer_instance
      epi_g := (Rep.epi_iff_surjective g).2 hg_surj }

  have hj0 : (f_B ≫ biprod.inl) ≫ g = 0 := by
    rw [Category.assoc, hinl_g, ← Category.assoc, w_B, zero_comp]
  let j : R_B ⟶ kernel g := kernel.lift g (f_B ≫ biprod.inl) hj0
  have hj : j ≫ f = f_B ≫ biprod.inl := kernel.lift_ι _ _ _
  haveI : Mono f₁ := hT₁.mono_f
  haveI : Mono f_B := hT_B.mono_f
  haveI : Mono SB.f := hSB.mono_f
  have hq0 : (f ≫ biprod.snd) ≫ (ShortComplex.mk f₁ g₁ w₁).g = 0 := by
    change (f ≫ biprod.snd) ≫ g₁ = 0
    rw [Category.assoc, ← hgρ, ← Category.assoc, w, zero_comp]
  let q : kernel g ⟶ R₁ := hT₁.exact.lift (f ≫ biprod.snd) hq0
  have hq : q ≫ f₁ = f ≫ biprod.snd := hT₁.exact.lift_f _ _
  have wR : j ≫ q = 0 := by
    rw [← cancel_mono f₁, Category.assoc, hq, ← Category.assoc, hj, Category.assoc, biprod.inl_snd, comp_zero,
      zero_comp]
  have hRexact : (ShortComplex.mk j q wR).Exact := by
        refine Rep.exact_mk_of_forall_exists_hom_eq j q wR fun r hr' => ?_

        have hsnd : (biprod.snd : P_B ⊞ P₁ ⟶ P₁).hom (f.hom r) = 0 := by
          rw [← capp, ← hq, capp, hr', map_zero]
        set p := (biprod.fst : P_B ⊞ P₁ ⟶ P_B).hom (f.hom r) with hpdef
        have htot : f.hom r = (biprod.inl : P_B ⟶ P_B ⊞ P₁).hom p := by
          have := congrArg (fun t : P_B ⊞ P₁ ⟶ P_B ⊞ P₁ => t.hom (f.hom r)) (biprod.total : _ = 𝟙 (P_B ⊞ P₁))
          simp only [Rep.add_hom] at this
          rw [hpdef]
          change ((biprod.fst : P_B ⊞ P₁ ⟶ P_B) ≫ (biprod.inl : P_B ⟶ P_B ⊞ P₁)).hom (f.hom r) +
              ((biprod.snd : P_B ⊞ P₁ ⟶ P₁) ≫ (biprod.inr : P₁ ⟶ P_B ⊞ P₁)).hom (f.hom r) =
            (𝟙 (P_B ⊞ P₁) : _ ⟶ _).hom (f.hom r) at this
          rw [capp biprod.snd, hsnd, map_zero, add_zero] at this
          exact this.symm

        have hgBp : g_B.hom p = 0 := by
          apply hinj SB.f inferInstance
          rw [map_zero, ← capp, ← hinl_g, capp, ← htot, ← capp, w]
          rfl
        obtain ⟨rB, hrB⟩ := hex f_B g_B w_B hT_B.exact p hgBp
        refine ⟨rB, ?_⟩
        apply hinj f inferInstance
        change f.hom (j.hom rB) = f.hom r
        rw [← capp, hj, capp, hrB, htot]
  have hRmono : Mono j := by
    haveI : Mono (j ≫ f) := by rw [hj]; exact mono_comp _ _
    exact mono_of_mono j f
  have hRepi : Epi q := by
        refine (Rep.epi_iff_surjective q).2 fun r₁ => ?_

        have h0 : SB.g.hom (lam.hom (f₁.hom r₁)) = 0 := by
          rw [← capp lam SB.g, hlam, ← capp f₁ g₁, w₁]
          rfl
        obtain ⟨b, hb⟩ := hex SB.f SB.g SB.zero hSB.exact _ h0
        obtain ⟨p, hp⟩ := hsurj g_B hT_B.epi_g b
        let x : ((P_B ⊞ P₁ : Rep.{0} ℤ G) : Type) := (biprod.inr : P₁ ⟶ P_B ⊞ P₁).hom (f₁.hom r₁) - (biprod.inl : P_B ⟶ P_B ⊞ P₁).hom p
        have hxdef : x = (biprod.inr : P₁ ⟶ P_B ⊞ P₁).hom (f₁.hom r₁) - (biprod.inl : P_B ⟶ P_B ⊞ P₁).hom p := rfl
        have hgx : g.hom x = 0 := by
          rw [hxdef, map_sub, ← capp biprod.inr g, hinr_g, ← capp biprod.inl g, hinl_g, capp, hp, hb, sub_self]
        obtain ⟨r, hr⟩ := hex f g w hTg.exact x hgx
        refine ⟨r, ?_⟩
        apply hinj f₁ inferInstance
        rw [← capp, hq, capp, hr, hxdef, map_sub, ← capp biprod.inr biprod.snd, biprod.inr_snd,
          ← capp biprod.inl biprod.snd, biprod.inl_snd]
        simp
  have hR : (ShortComplex.mk j q wR).ShortExact := { exact := hRexact, mono_f := hRmono, epi_g := hRepi }

  refine ⟨kernel g, f, g, w, hTg, j, q, wR, hR, hj.symm, hinl_g.symm, hq.symm, hgρ⟩

theorem solution
    {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (p : ℕ) [Fact p.Prime]
    {SB : ShortComplex (Rep ℤ G)} (hSB : SB.ShortExact) [Fintype SB.X₁] [Fintype SB.X₃]
    (hB₁ : ∀ b : SB.X₃, p • b = 0)
    (N : Subgroup G) (hpN : p ∣ Nat.card ↥N) (hN : ∀ g ∈ N, ∀ b : SB.X₃, SB.X₃.ρ g b = b)

    {R_B P_B : Rep ℤ G} (f_B : R_B ⟶ P_B) (g_B : P_B ⟶ SB.X₁) (w_B : f_B ≫ g_B = 0)
    (hT_B : (ShortComplex.mk f_B g_B w_B).ShortExact)
    (hP_B : ∀ (X Y : Rep ℤ G) (e : X ⟶ Y), Function.Surjective e.hom → ∀ χ : P_B ⟶ Y, ∃ χ' : P_B ⟶ X, χ' ≫ e = χ)
    {R_I P_I : Rep ℤ G} (f_I : R_I ⟶ P_I) (g_I : P_I ⟶ SB.X₂) (w_I : f_I ≫ g_I = 0)
    (hT_I : (ShortComplex.mk f_I g_I w_I).ShortExact)
    (hP_I : ∀ (X Y : Rep ℤ G) (e : X ⟶ Y), Function.Surjective e.hom → ∀ χ : P_I ⟶ Y, ∃ χ' : P_I ⟶ X, χ' ≫ e = χ)

    (ιR : R_B ⟶ R_I) (ιP : P_B ⟶ P_I) (sq₁ : f_B ≫ ιP = ιR ≫ f_I) (sq₂ : g_B ≫ SB.f = ιP ≫ g_I)
    (φ : R_B ⟶ C)
    (hφ : ∀ y : groupCohomology SB.X₁ 1,
      (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) = 0) :
    ∃ (ψ : R_I ⟶ C) (χ : P_B ⟶ C), φ = ιR ≫ ψ + f_B ≫ χ := by
  classical

  have hmap_comp : ∀ {X Y Z : Rep ℤ G} (a : X ⟶ Y) (b : Y ⟶ Z) (n : ℕ) (x : groupCohomology X n),
      (groupCohomology.map (MonoidHom.id G) (a ≫ b) n).hom x =
        (groupCohomology.map (MonoidHom.id G) b n).hom ((groupCohomology.map (MonoidHom.id G) a n).hom x) := by
    intro X Y Z a b n x
    rw [groupCohomology.map_id_comp, ModuleCat.comp_apply]

  have hXB : (Rep.relationSeqInt SB.X₁).ShortExact := Rep.relationSeqInt_shortExact SB.X₁
  have hX₁ : (Rep.relationSeqInt SB.X₃).ShortExact := Rep.relationSeqInt_shortExact SB.X₃
  have hfree : ∀ (A : Type) (X Y : Rep ℤ G) (e : X ⟶ Y), Function.Surjective e.hom →
      ∀ χ : Rep.free ℤ G A ⟶ Y, ∃ χ' : Rep.free ℤ G A ⟶ X, χ' ≫ e = χ := by
    intro A X Y e he χ
    haveI : Epi e := (Rep.epi_iff_surjective e).2 he
    exact ⟨Projective.factorThru χ e, Projective.factorThru_comp χ e⟩

  obtain ⟨cR, cP, hc₁, hc₂⟩ := KerStep.exists_comparison (Rep.relationModuleInt.ι SB.X₁) (Rep.freeCover SB.X₁) f_B g_B w_B hT_B
    (hfree _) (Rep.relationModuleInt_ι_comp_freeCover SB.X₁) (𝟙 _)
  obtain ⟨dR, dP, hd₁, hd₂⟩ := KerStep.exists_comparison f_B g_B (Rep.relationModuleInt.ι SB.X₁) (Rep.freeCover SB.X₁)
    (Rep.relationModuleInt_ι_comp_freeCover SB.X₁) hXB hP_B w_B (𝟙 _)

  have hφ' : ∀ y : groupCohomology SB.X₁ 1,
      (groupCohomology.map (MonoidHom.id G) (cR ≫ φ) 2).hom ((groupCohomology.δ hXB 1 2 rfl).hom y) = 0 := by
    intro y
    let ψc : Rep.relationSeqInt SB.X₁ ⟶ ShortComplex.mk f_B g_B w_B :=
      { τ₁ := cR, τ₂ := cP, τ₃ := 𝟙 _, comm₁₂ := hc₁.symm, comm₂₃ := by
          change cP ≫ g_B = Rep.freeCover SB.X₁ ≫ 𝟙 _
          exact hc₂.symm }
    have h := HomologicalComplex.HomologySequence.δ_naturality
      ((groupCohomology.cochainsFunctor ℤ G).mapShortComplex.map ψc)
      (groupCohomology.map_cochainsFunctor_shortExact hXB) (groupCohomology.map_cochainsFunctor_shortExact hT_B) 1 2 rfl
    have h' := congrArg (fun f => (ModuleCat.Hom.hom f) y) h

    rw [hmap_comp]
    have h'' : (groupCohomology.map (MonoidHom.id G) cR 2).hom ((groupCohomology.δ hXB 1 2 rfl).hom y) =
        (groupCohomology.δ hT_B 1 2 rfl).hom y := by
      refine h'.trans ?_
      change (groupCohomology.δ hT_B 1 2 rfl).hom ((groupCohomology.map (MonoidHom.id G) (𝟙 SB.X₁) 1).hom y) = _
      rw [groupCohomology.map_id]
      rfl
    rw [h'', hφ]

  obtain ⟨ψ₀, hψ₀⟩ := (Rep.forall_map_delta_eq_zero_iff_exists_eq_sum_rho C u h1 h2card h2gen SB.X₁ hXB (cR ≫ φ)).1 hφ'
  have hN₀ : cR ≫ φ = KerStep.norm (Rep.relationModuleInt SB.X₁) C ψ₀ := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro x
    change (cR ≫ φ).hom x = (KerStep.norm _ C ψ₀).hom x
    rw [KerStep.norm_hom_apply, hψ₀]
    rfl

  obtain ⟨t, ht⟩ := KerStep.exists_sub_eq_comp f_B g_B f_B g_B w_B hT_B (𝟙 _) (dR ≫ cR) (𝟙 _) (dP ≫ cP) (𝟙 _)
    (by rw [← Category.assoc, hd₁, Category.assoc, hc₁, Category.assoc])
    (by rw [Category.assoc, ← hc₂, Category.comp_id, ← Category.comp_id g_B, hd₂, Category.comp_id]) (by simp) (by simp)
  have hφN : φ = KerStep.norm R_B C (ψ₀.comp (KerStep.addHom dR)) - f_B ≫ (t ≫ φ) := by
    have h1 : dR ≫ cR = f_B ≫ t + 𝟙 _ := by rw [← ht]; abel
    calc φ = 𝟙 _ ≫ φ := (Category.id_comp φ).symm
      _ = (dR ≫ cR - f_B ≫ t) ≫ φ := by rw [h1]; abel_nf
      _ = dR ≫ (cR ≫ φ) - f_B ≫ (t ≫ φ) := by rw [Preadditive.sub_comp, Category.assoc, Category.assoc]
      _ = KerStep.norm R_B C (ψ₀.comp (KerStep.addHom dR)) - f_B ≫ (t ≫ φ) := by
          rw [hN₀, KerStep.comp_norm]
          rfl

  obtain ⟨R, fR, gR, wR, hTR, j, q, wjq, hjq, s₁, s₂, s₃, s₄⟩ :=
    KerStep.horseshoe hSB f_B g_B w_B hT_B (Rep.relationModuleInt.ι SB.X₃) (Rep.freeCover SB.X₃)
      (Rep.relationModuleInt_ι_comp_freeCover SB.X₃) hX₁ (hfree _)

  haveI : Module.Free ℤ (Rep.relationCarrier SB.X₃) := Rep.moduleFree_relationCarrier SB.X₃
  obtain ⟨r, hr⟩ := KerStep.exists_retraction (Rep.relationRepInt SB.X₃) j q wjq hjq

  set ψt : R ⟶ C := KerStep.norm R C ((ψ₀.comp (KerStep.addHom dR)).comp r) with hψt
  have hjψ : j ≫ ψt = KerStep.norm R_B C (ψ₀.comp (KerStep.addHom dR)) := by
    rw [hψt, KerStep.comp_norm]
    congr 1
    ext x
    simp only [AddMonoidHom.comp_apply, KerStep.addHom_apply, hr]

  obtain ⟨eR, eP, he₁, he₂⟩ := KerStep.exists_comparison f_I g_I fR gR wR hTR hP_I w_I (𝟙 _)
  obtain ⟨t', ht'⟩ := KerStep.exists_sub_eq_comp f_B g_B fR gR wR hTR SB.f (ιR ≫ eR) j (ιP ≫ eP) biprod.inl
    (by rw [← Category.assoc, sq₁, Category.assoc, he₁, Category.assoc])
    (by rw [sq₂, Category.assoc, ← he₂, Category.comp_id]) s₁ s₂

  refine ⟨eR ≫ ψt, -(t' ≫ ψt) - t ≫ φ, ?_⟩
  have hj' : j = ιR ≫ eR - f_B ≫ t' := by rw [← ht']; abel
  conv_lhs => rw [hφN, ← hjψ, hj']
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_neg, Category.assoc, Category.assoc]
  abel

end S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective
end P2MW
export P2MW.S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective (solution)

-- Prove2me | solution 1 for Rep.IsTateCupProduct.cupEv_dual_right_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4520f9bc-2f59-5ea7-869f-eeca23189d19

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Theorems.Thm_Rep_isZero_tateCohomology_of_bijective_card_nsmul
import Theorems.Thm_Rep_bijective_tateDelta_of_isZero
import Theorems.Thm_Rep_tateDelta_naturality
import Theorems.Thm_Rep_IsTateCupProduct_cupEv_characterDual_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_IsTateCupProduct_cupEv_dual_right_eq_zero

set_option autoImplicit false
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"
universe u
namespace P2mS26IntR0

section generic

variable {k G : Type u} [CommRing k] [Group G]

theorem shortExact_of_hom {S : ShortComplex (Rep.{u} k G)} (hf : Function.Injective S.f.hom)
    (hg : Function.Surjective S.g.hom) (hex : ∀ y : S.X₂, S.g.hom y = 0 → ∃ x : S.X₁, S.f.hom x = y) :
    S.ShortExact where
  exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _
    ((ShortComplex.moduleCat_exact_iff _).2 fun y hy => hex y hy)
  mono_f := (Rep.mono_iff_injective _).2 hf
  epi_g := (Rep.epi_iff_surjective _).2 hg

theorem range_eq_ker_of_shortExact {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) :
    LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
  (hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker

def ofD (M W : Rep.{u} k G) (f : (ihom M).obj W) : (M : Type u) →ₗ[k] W := f

def toD (M W : Rep.{u} k G) (f : (M : Type u) →ₗ[k] W) : (ihom M).obj W := f
@[scoped simp] theorem ofD_toD (M W : Rep.{u} k G) (f : (M : Type u) →ₗ[k] W) : ofD M W (toD M W f) = f := rfl
@[scoped simp] theorem toD_ofD (M W : Rep.{u} k G) (f : (ihom M).obj W) : toD M W (ofD M W f) = f := rfl

theorem ihom_map_hom_apply (M : Rep.{u} k G) {X Y : Rep.{u} k G} (φ : X ⟶ Y) (f : (ihom M).obj X) :
    ((ihom M).map φ).hom f = toD M Y (φ.hom.toLinearMap ∘ₗ ofD M X f) := rfl

noncomputable def ihomSC (M : Rep.{u} k G) (X : ShortComplex (Rep.{u} k G)) : ShortComplex (Rep.{u} k G) where
  X₁ := (ihom M).obj X.X₁
  X₂ := (ihom M).obj X.X₂
  X₃ := (ihom M).obj X.X₃
  f := (ihom M).map X.f
  g := (ihom M).map X.g
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => LinearMap.ext fun m => by
    exact congrArg (fun φ : X.X₁ ⟶ X.X₃ => φ.hom (ofD M _ f m)) X.zero))

noncomputable def evSC (M : Rep.{u} k G) (X : ShortComplex (Rep.{u} k G)) :
    (ihomSC M X).map (MonoidalCategory.tensorLeft M) ⟶ X where
  τ₁ := (ihom.ev M).app X.X₁
  τ₂ := (ihom.ev M).app X.X₂
  τ₃ := (ihom.ev M).app X.X₃
  comm₁₂ := ((ihom.ev M).naturality X.f).symm
  comm₂₃ := ((ihom.ev M).naturality X.g).symm

variable [Fintype G]

theorem ev_cup_tateDelta {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup)
    (M : Rep.{u} k G) {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hE : (ihomSC M X).ShortExact) (hME : ((ihomSC M X).map (MonoidalCategory.tensorLeft M)).ShortExact)
    (p q r : ℤ) (h : p + q = r) (x : M.tateCohomology p) (a : ((ihom M).obj X.X₃).tateCohomology q) :
    ((p.negOnePow : ℤ) : k) • (Rep.tateMap ((ihom.ev M).app X.X₁) (r + 1)).hom
        (cup M ((ihom M).obj X.X₁) p (q + 1) (r + 1) (by omega) x ((Rep.tateδ hE q).hom a))
      = (Rep.tateδ hX r).hom
          ((Rep.tateMap ((ihom.ev M).app X.X₃) r).hom (cup M ((ihom M).obj X.X₃) p q r h x a)) := by
  have hcd := hcup.cup_delta M hE hME p q r h x a
  have hnat := Rep.tateDelta_naturality hME hX (evSC M X) r
  have hnat' : ∀ w, (Rep.tateMap ((ihom.ev M).app X.X₁) (r + 1)).hom ((Rep.tateδ hME r).hom w)
      = (Rep.tateδ hX r).hom ((Rep.tateMap ((ihom.ev M).app X.X₃) r).hom w) := fun w => by
    have := congrArg (fun φ => φ.hom w) hnat
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  have h2 := congrArg (Rep.tateMap ((ihom.ev M).app X.X₁) (r + 1)).hom hcd
  have h3 : (Rep.tateMap ((ihom.ev M).app X.X₁) (r + 1)).hom
      ((((p.negOnePow : ℤ) : k)) • cup M ((ihom M).obj X.X₁) p (q + 1) (r + 1) (by omega) x ((Rep.tateδ hE q).hom a))
      = ((p.negOnePow : ℤ) : k) • (Rep.tateMap ((ihom.ev M).app X.X₁) (r + 1)).hom
          (cup M ((ihom M).obj X.X₁) p (q + 1) (r + 1) (by omega) x ((Rep.tateδ hE q).hom a)) := map_smul _ _ _
  exact (h3.symm.trans h2.symm).trans (hnat' _)

theorem bijective_card_nsmul_ihom (M W : Rep.{u} k G)
    (hW : Function.Bijective (fun w : W => Fintype.card G • w)) :
    Function.Bijective (fun a : ((ihom M).obj W) => Fintype.card G • a) := by
  let L : (W : Type u) →ₗ[k] W := Fintype.card G • LinearMap.id
  let E : (W : Type u) ≃ₗ[k] W := LinearEquiv.ofBijective L hW
  constructor
  · intro a b hab
    apply_fun ofD M W at hab
    change ofD M W a = ofD M W b
    refine LinearMap.ext fun m => hW.1 ?_
    have := LinearMap.congr_fun hab m
    exact this
  · intro b
    refine ⟨toD M W (E.symm.toLinearMap ∘ₗ ofD M W b), ?_⟩
    change ofD M W (Fintype.card G • toD M W (E.symm.toLinearMap ∘ₗ ofD M W b)) = ofD M W b
    refine LinearMap.ext fun m => ?_
    change E (E.symm (ofD M W b m)) = ofD M W b m
    exact E.apply_symm_apply _

end generic

section integral

variable {G : Type} [Group G]

def zlin {A B : Type} [AddCommGroup A] [AddCommGroup B] [mA : Module ℤ A] [mB : Module ℤ B] (f : A →+ B) :
    A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' z a := (congrArg f (int_smul_eq_zsmul mA z a)).trans
    ((map_zsmul f z a).trans (int_smul_eq_zsmul mB z (f a)).symm)

@[scoped simp] theorem zlin_apply {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]
    (f : A →+ B) (a : A) : zlin f a = f a := rfl

abbrev QZ : Type := AddCircle (1 : ℚ)

variable (G) in

noncomputable def Zsc : ShortComplex (Rep ℤ G) where
  X₁ := Rep.trivial ℤ G ℤ
  X₂ := Rep.trivial ℤ G ℚ
  X₃ := Rep.trivial ℤ G QZ
  f := Rep.ofHom ⟨zlin (Int.castAddHom ℚ), fun _ => rfl⟩
  g := Rep.ofHom ⟨zlin (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))), fun _ => rfl⟩
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun n => by
    change ((n : ℚ) : QZ) = 0
    exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).2 ⟨n, by simp⟩))

theorem Zsc_f_apply (n : ℤ) : (Zsc G).f.hom n = (n : ℚ) := rfl
theorem Zsc_g_apply (x : ℚ) : (Zsc G).g.hom x = (x : QZ) := rfl

theorem Zsc_shortExact : (Zsc G).ShortExact := by
  refine shortExact_of_hom ?_ ?_ ?_
  · intro a b hab
    exact Int.cast_injective (α := ℚ) hab
  · intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact ⟨x, rfl⟩
  · intro y hy
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).1 hy
    exact ⟨n, by rw [Zsc_f_apply, ← hn, zsmul_eq_mul, mul_one]⟩

theorem ihomSC_Z_shortExact (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V) :
    (ihomSC (Rep.of ρ) (Zsc G)).ShortExact := by
  refine shortExact_of_hom ?_ ?_ ?_
  · intro a b hab
    apply_fun ofD (Rep.of ρ) _ at hab ⊢
    · refine LinearMap.ext fun v => ?_
      have := LinearMap.congr_fun hab v
      exact Int.cast_injective (α := ℚ) this
    · exact fun a b h => h
  · intro c
    obtain ⟨h, hh⟩ := Module.projective_lifting_property (Zsc G).g.hom.toLinearMap (ofD (Rep.of ρ) _ c)
      (fun y => by obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y; exact ⟨x, rfl⟩)
    exact ⟨toD (Rep.of ρ) _ h, congrArg (toD (Rep.of ρ) _) hh⟩
  · intro b hb
    have hb' : ∀ v : V, ∃ n : ℤ, (Zsc G).f.hom n = ofD (Rep.of ρ) _ b v := fun v => by
      have hv : (Zsc G).g.hom (ofD (Rep.of ρ) _ b v) = 0 := by
        have := congrArg (fun φ => ofD (Rep.of ρ) _ φ v) hb
        exact this
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).1 hv
      exact ⟨n, by rw [Zsc_f_apply, ← hn, zsmul_eq_mul, mul_one]⟩
    have hinj : Function.Injective (Zsc G).f.hom.toLinearMap := fun a b hab => Int.cast_injective (α := ℚ) hab
    have hmem : ∀ v : V, ofD (Rep.of ρ) _ b v ∈ LinearMap.range (Zsc G).f.hom.toLinearMap := fun v => by
      obtain ⟨n, hn⟩ := hb' v
      exact ⟨n, hn⟩
    refine ⟨toD (Rep.of ρ) _ ((LinearEquiv.ofInjective _ hinj).symm.toLinearMap ∘ₗ
      LinearMap.codRestrict _ (ofD (Rep.of ρ) _ b) hmem), ?_⟩
    apply_fun ofD (Rep.of ρ) _
    · refine LinearMap.ext fun v => ?_
      change (Zsc G).f.hom.toLinearMap ((LinearEquiv.ofInjective _ hinj).symm
        (LinearMap.codRestrict _ (ofD (Rep.of ρ) _ b) hmem v)) = ofD (Rep.of ρ) _ b v
      rw [← LinearEquiv.ofInjective_apply (h := hinj), LinearEquiv.apply_symm_apply]
      rfl
    · exact fun a b h => h

theorem ihomSC_Z_tensorLeft_shortExact (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V) :
    ((ihomSC (Rep.of ρ) (Zsc G)).map (MonoidalCategory.tensorLeft (Rep.of ρ))).ShortExact := by
  have hE := ihomSC_Z_shortExact V ρ
  set E := ihomSC (Rep.of ρ) (Zsc G)
  have hinj : Function.Injective E.f.hom.toLinearMap := (Rep.mono_iff_injective E.f).1 hE.mono_f
  have hsurj : Function.Surjective E.g.hom.toLinearMap := (Rep.epi_iff_surjective E.g).1 hE.epi_g
  have hexact : Function.Exact E.f.hom.toLinearMap E.g.hom.toLinearMap :=
    LinearMap.exact_iff.2 (range_eq_ker_of_shortExact hE).symm
  have hT : Function.Exact (E.f.hom.toLinearMap.lTensor V) (E.g.hom.toLinearMap.lTensor V) :=
    lTensor_exact V hexact hsurj
  refine shortExact_of_hom ?_ ?_ ?_
  · change Function.Injective (E.f.hom.toLinearMap.lTensor V)
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · change Function.Surjective (E.g.hom.toLinearMap.lTensor V)
    exact LinearMap.lTensor_surjective _ hsurj
  · intro y hy
    obtain ⟨x, hx⟩ := (hT y).1 hy
    exact ⟨x, hx⟩

variable [Fintype G]

theorem bijective_card_nsmul_rat : Function.Bijective (fun a : (Rep.trivial ℤ G ℚ) => Fintype.card G • a) := by
  have hG : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro a b hab
    have : (Fintype.card G : ℚ) * a = (Fintype.card G : ℚ) * b := by
      simpa only [nsmul_eq_mul] using hab
    exact mul_left_cancel₀ hG this
  · intro b
    refine ⟨(show ℚ from b) / Fintype.card G, ?_⟩
    change Fintype.card G • ((show ℚ from b) / Fintype.card G) = b
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hG]

theorem isZero_tateCohomology_rat (n : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.trivial ℤ G ℚ).tateCohomology n) :=
  Rep.isZero_tateCohomology_of_bijective_card_nsmul _ bijective_card_nsmul_rat n

theorem isZero_tateCohomology_ihom_rat (M : Rep ℤ G) (n : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom M).obj (Rep.trivial ℤ G ℚ)).tateCohomology n) :=
  Rep.isZero_tateCohomology_of_bijective_card_nsmul _
    (bijective_card_nsmul_ihom M (Rep.trivial ℤ G ℚ) bijective_card_nsmul_rat) n

theorem bijective_tateDelta_Z (n : ℤ) : Function.Bijective (Rep.tateδ (Zsc_shortExact (G := G)) n).hom :=
  Rep.bijective_tateDelta_of_isZero _ n (isZero_tateCohomology_rat n) (isZero_tateCohomology_rat (n + 1))

theorem bijective_tateDelta_E (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V) (n : ℤ) :
    Function.Bijective (Rep.tateδ (ihomSC_Z_shortExact (G := G) V ρ) n).hom :=
  Rep.bijective_tateDelta_of_isZero _ n (isZero_tateCohomology_ihom_rat (Rep.of ρ) n)
    (isZero_tateCohomology_ihom_rat (Rep.of ρ) (n + 1))

end integral

end P2mS26IntR0
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_cupEv_dual_right_eq_zero.P2mS26IntR0"

open P2mS26IntR0 in
theorem solution {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V)
    (p q : ℤ) (h : p + q = 0) (b : ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)).tateCohomology q)
    (hb : ∀ x : (Rep.of ρ).tateCohomology p,
      (Rep.tateMap ((ihom.ev (Rep.of ρ)).app (Rep.trivial ℤ G ℤ)) 0).hom
        (cup (Rep.of ρ) ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) p q 0 h x b) = 0) :
    b = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q' : ℤ, q = q' + 1 := ⟨q - 1, by omega⟩
  have h' : p + q = -1 := by omega
  have hE := ihomSC_Z_shortExact (G := G) V ρ
  have hME := ihomSC_Z_tensorLeft_shortExact (G := G) V ρ
  obtain ⟨a, rfl⟩ := (bijective_tateDelta_E (G := G) V ρ q).2 b
  suffices ha : a = 0 by rw [ha]; exact map_zero _
  refine hcup.cupEv_characterDual_eq_zero (Rep.of ρ) p q h' a fun x => ?_
  have key := ev_cup_tateDelta hcup (Rep.of ρ) Zsc_shortExact hE hME p q (-1) h' x a
  have h0 : (Rep.tateMap ((ihom.ev (Rep.of ρ)).app (Zsc G).X₁) (-1 + 1)).hom
      (cup (Rep.of ρ) ((ihom (Rep.of ρ)).obj (Zsc G).X₁) p (q + 1) (-1 + 1) (by omega) x
        ((Rep.tateδ hE q).hom a)) = 0 := hb x
  rw [h0, smul_zero] at key
  exact (bijective_tateDelta_Z (G := G) (-1)).1 (key.symm.trans (map_zero _).symm)

end S_Rep_IsTateCupProduct_cupEv_dual_right_eq_zero
end P2MW
export P2MW.S_Rep_IsTateCupProduct_cupEv_dual_right_eq_zero (solution)

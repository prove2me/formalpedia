-- Prove2me | solution 1 for Rep.IsTateCupProduct.injective_cupEv_characterDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f60dd439-e62e-59a4-bf0a-8e8553088095

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Theorems.Thm_Rep_shortExact_map_tensorRight_of_splitting
import Theorems.Thm_Rep_shortExact_map_tensorLeft_of_splitting
import Theorems.Thm_Rep_dimShiftDown_shortExact
import Theorems.Thm_Rep_dimShiftUp_shortExact
import Theorems.Thm_Rep_bijective_tateDelta_dimShiftDown
import Theorems.Thm_Rep_bijective_tateDelta_dimShiftUp
import Theorems.Thm_Rep_bijective_tateDelta_of_isZero
import Theorems.Thm_Rep_isZero_tateCohomology_ihom_indBot
import Theorems.Thm_Rep_indBotPi_indBotSigma
import Theorems.Thm_Rep_indBotr_indBotIota
import Theorems.Thm_Rep_tateMap_tateDelta_add_tateMap_tateDelta_eq_zero
import Theorems.Thm_Rep_IsTateCupProduct_injective_cupEv_negOne_characterDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_IsTateCupProduct_injective_cupEv_characterDual

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

attribute [local instance 2000] Rep.hV2 Rep.hV1

namespace P2mS26FDpL

noncomputable section

section generic
variable {k G : Type u} [CommRing k] [Group G]

def ofD (M W : Rep.{u} k G) (f : (ihom M).obj W) : (M : Type u) →ₗ[k] W := f

def toD (M W : Rep.{u} k G) (f : (M : Type u) →ₗ[k] W) : (ihom M).obj W := f

@[scoped simp] lemma ofD_toD (M W : Rep.{u} k G) (f : (M : Type u) →ₗ[k] W) : ofD M W (toD M W f) = f := rfl
@[scoped simp] lemma toD_ofD (M W : Rep.{u} k G) (f : (ihom M).obj W) : toD M W (ofD M W f) = f := rfl

lemma ofD_ρ (M W : Rep.{u} k G) (g : G) (f : (ihom M).obj W) :
    ofD M W (((ihom M).obj W).ρ g f) = W.ρ g ∘ₗ ofD M W f ∘ₗ M.ρ g⁻¹ :=
  Rep.ihom_obj_ρ_apply (A := M) (B := W) g (ofD M W f)

lemma ev_tmul (M W : Rep.{u} k G) (m : M) (f : (ihom M).obj W) :
    ((ihom.ev M).app W).hom (m ⊗ₜ[k] f : (M ⊗ (ihom M).obj W : Rep.{u} k G)) = ofD M W f m := by
  change ((ihom.ev M).app W).hom.toLinearMap (m ⊗ₜ[k] f) = ofD M W f m
  rw [Rep.ihom_ev_app_hom]
  rfl

def preD (W : Rep.{u} k G) {A B : Rep.{u} k G} (φ : A ⟶ B) : (ihom B).obj W ⟶ (ihom A).obj W :=
  Rep.ofHom ⟨LinearMap.lcomp k W φ.hom.toLinearMap, fun g => LinearMap.ext fun f => by
    change toD A W (ofD B W (((ihom B).obj W).ρ g f) ∘ₗ φ.hom.toLinearMap)
      = ((ihom A).obj W).ρ g (toD A W (ofD B W f ∘ₗ φ.hom.toLinearMap))
    apply congrArg (toD A W) (?_ : _ = ofD A W (((ihom A).obj W).ρ g (toD A W (ofD B W f ∘ₗ φ.hom.toLinearMap))))
    rw [ofD_ρ, ofD_ρ, ofD_toD]
    refine LinearMap.ext fun a => ?_
    change W.ρ g (ofD B W f (B.ρ g⁻¹ (φ.hom a))) = W.ρ g (ofD B W f (φ.hom (A.ρ g⁻¹ a)))
    rw [Rep.hom_comm_apply]⟩

lemma ofD_preD (W : Rep.{u} k G) {A B : Rep.{u} k G} (φ : A ⟶ B) (f : (ihom B).obj W) :
    ofD A W ((preD W φ).hom f) = ofD B W f ∘ₗ φ.hom.toLinearMap := rfl

def dualSC (W : Rep.{u} k G) (X : ShortComplex (Rep.{u} k G)) : ShortComplex (Rep.{u} k G) where
  X₁ := (ihom X.X₃).obj W
  X₂ := (ihom X.X₂).obj W
  X₃ := (ihom X.X₁).obj W
  f := preD W X.g
  g := preD W X.f
  zero := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    change toD X.X₁ W ((ofD X.X₃ W f ∘ₗ X.g.hom.toLinearMap) ∘ₗ X.f.hom.toLinearMap) = toD X.X₁ W 0
    rw [LinearMap.comp_assoc, show X.g.hom.toLinearMap ∘ₗ X.f.hom.toLinearMap = 0 from
      LinearMap.ext fun x => Rep.seam_g_f_apply X x, LinearMap.comp_zero]

variable {X : ShortComplex (Rep.{u} k G)}

lemma seam_exact (hX : X.ShortExact) : Function.Exact X.f.hom.toLinearMap X.g.hom.toLinearMap :=
  LinearMap.exact_iff.2 (Rep.seam_range_eq_ker hX).symm

lemma mem_range (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (x : X.X₂) :
    x - s (X.g.hom x) ∈ LinearMap.range X.f.hom.toLinearMap := by
  rw [Rep.seam_range_eq_ker hX, LinearMap.mem_ker]
  change X.g.hom (x - s (X.g.hom x)) = 0
  rw [map_sub, hs, sub_self]

def retr (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) : (X.X₂ : Type u) →ₗ[k] X.X₁ :=
  (LinearEquiv.ofInjective X.f.hom.toLinearMap (Rep.seam_f_injective hX)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range X.f.hom.toLinearMap) (LinearMap.id - s ∘ₗ X.g.hom.toLinearMap)
      (fun x => mem_range hX s hs x)

lemma f_retr (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (x : X.X₂) :
    X.f.hom (retr hX s hs x) = x - s (X.g.hom x) :=
  congrArg Subtype.val ((LinearEquiv.ofInjective X.f.hom.toLinearMap (Rep.seam_f_injective hX)).apply_symm_apply
    ⟨x - s (X.g.hom x), mem_range hX s hs x⟩)

lemma retr_f (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (a : X.X₁) :
    retr hX s hs (X.f.hom a) = a :=
  Rep.seam_f_injective hX (by rw [f_retr, Rep.seam_g_f_apply, map_zero, sub_zero])

lemma f_retr_add_s_g (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (x : X.X₂) :
    X.f.hom (retr hX s hs x) + s (X.g.hom x) = x := by
  rw [f_retr, sub_add_cancel]

lemma dualSC_shortExact (W : Rep.{u} k G) (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂)
    (hs : ∀ x : X.X₃, X.g.hom (s x) = x) : (dualSC W X).ShortExact := by
  have hg := Rep.seam_g_surjective hX
  exact
    { exact := by
        refine (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ ((ShortComplex.moduleCat_exact_iff _).2 ?_)
        intro (χ : (ihom X.X₂).obj W) hχ
        have hχ' : ofD X.X₂ W χ ∘ₗ X.f.hom.toLinearMap = 0 := congrArg (ofD X.X₁ W) hχ
        refine ⟨toD X.X₃ W (ofD X.X₂ W χ ∘ₗ s), ?_⟩
        change toD X.X₂ W ((ofD X.X₂ W χ ∘ₗ s) ∘ₗ X.g.hom.toLinearMap) = toD X.X₂ W (ofD X.X₂ W χ)
        congr 1
        refine LinearMap.ext fun x => ?_
        change ofD X.X₂ W χ (s (X.g.hom x)) = ofD X.X₂ W χ x
        conv_rhs => rw [← f_retr_add_s_g hX s hs x]
        rw [map_add, show ofD X.X₂ W χ (X.f.hom (retr hX s hs x)) = 0 from LinearMap.congr_fun hχ' _, zero_add]
      mono_f := (Rep.mono_iff_injective _).2 (fun (ψ ψ' : (ihom X.X₃).obj W) h => by
        have h' : ofD X.X₃ W ψ ∘ₗ X.g.hom.toLinearMap = ofD X.X₃ W ψ' ∘ₗ X.g.hom.toLinearMap := congrArg (ofD X.X₂ W) h
        apply congrArg (toD X.X₃ W) (?_ : ofD X.X₃ W ψ = ofD X.X₃ W ψ')
        refine LinearMap.ext fun y => ?_
        obtain ⟨x, rfl⟩ := hg y
        exact LinearMap.congr_fun h' x)
      epi_g := (Rep.epi_iff_surjective _).2 (fun (χ : (ihom X.X₁).obj W) =>
        ⟨toD X.X₂ W (ofD X.X₁ W χ ∘ₗ retr hX s hs), congrArg (toD X.X₁ W)
          (LinearMap.ext fun a => congrArg (ofD X.X₁ W χ) (retr_f hX s hs a) :
            ofD X.X₁ W χ ∘ₗ retr hX s hs ∘ₗ X.f.hom.toLinearMap = ofD X.X₁ W χ)⟩) }

def dualSection (W : Rep.{u} k G) (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) :
    ((dualSC W X).X₃ : Type u) →ₗ[k] (dualSC W X).X₂ :=
  LinearMap.lcomp k W (retr hX s hs)

lemma g_dualSection (W : Rep.{u} k G) (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x)
    (χ : (dualSC W X).X₃) : (dualSC W X).g.hom (dualSection W hX s hs χ) = χ :=
  congrArg (toD X.X₁ W) (LinearMap.ext fun a => congrArg (ofD X.X₁ W χ) (retr_f hX s hs a) :
    ofD X.X₁ W χ ∘ₗ retr hX s hs ∘ₗ X.f.hom.toLinearMap = ofD X.X₁ W χ)

lemma whiskerRight_tmul {P Q : Rep.{u} k G} (ψ : P ⟶ Q) (C : Rep.{u} k G) (x : P) (c : C) :
    (ψ ▷ C).hom (x ⊗ₜ[k] c : (P ⊗ C : Rep.{u} k G)) = (ψ.hom x ⊗ₜ[k] c : (Q ⊗ C : Rep.{u} k G)) := by
  change (ψ ▷ C).hom.toLinearMap (x ⊗ₜ[k] c) = _
  rw [Rep.hom_whiskerRight, Representation.IntertwiningMap.toLinearMap_rTensor, LinearMap.rTensor_tmul]
  rfl

lemma whiskerLeft_tmul (C : Rep.{u} k G) {P Q : Rep.{u} k G} (ψ : P ⟶ Q) (c : C) (x : P) :
    (C ◁ ψ).hom (c ⊗ₜ[k] x : (C ⊗ P : Rep.{u} k G)) = (c ⊗ₜ[k] ψ.hom x : (C ⊗ Q : Rep.{u} k G)) := by
  change (C ◁ ψ).hom.toLinearMap (c ⊗ₜ[k] x) = _
  rw [Rep.hom_whiskerLeft, Representation.IntertwiningMap.toLinearMap_lTensor, LinearMap.lTensor_tmul]
  rfl

lemma ev_compat_f (W : Rep.{u} k G) (X : ShortComplex (Rep.{u} k G)) :
    X.f ▷ (dualSC W X).X₂ ≫ (ihom.ev X.X₂).app W = X.X₁ ◁ (dualSC W X).g ≫ (ihom.ev X.X₁).app W := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun x χ => ?_))
  change ((ihom.ev X.X₂).app W).hom ((X.f ▷ (dualSC W X).X₂).hom (x ⊗ₜ[k] χ))
    = ((ihom.ev X.X₁).app W).hom ((X.X₁ ◁ (dualSC W X).g).hom (x ⊗ₜ[k] χ))
  rw [whiskerRight_tmul, whiskerLeft_tmul]
  refine (ev_tmul X.X₂ W (X.f.hom x) χ).trans ?_
  refine Eq.trans ?_ (ev_tmul X.X₁ W x ((dualSC W X).g.hom χ)).symm
  rfl

lemma ev_compat_g (W : Rep.{u} k G) (X : ShortComplex (Rep.{u} k G)) :
    X.X₂ ◁ (dualSC W X).f ≫ (ihom.ev X.X₂).app W = X.g ▷ (dualSC W X).X₁ ≫ (ihom.ev X.X₃).app W := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun x ψ => ?_))
  change ((ihom.ev X.X₂).app W).hom ((X.X₂ ◁ (dualSC W X).f).hom (x ⊗ₜ[k] ψ))
    = ((ihom.ev X.X₃).app W).hom ((X.g ▷ (dualSC W X).X₁).hom (x ⊗ₜ[k] ψ))
  rw [whiskerRight_tmul, whiskerLeft_tmul]
  refine (ev_tmul X.X₂ W x ((dualSC W X).f.hom ψ)).trans ?_
  refine Eq.trans ?_ (ev_tmul X.X₃ W (X.g.hom x) ψ).symm
  rfl

variable [Fintype G]

theorem pair_cup {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (hX : X.ShortExact)
    (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (W : Rep.{u} k G)
    (p j n : ℤ) (h : p + j = n) (x : X.X₃.tateCohomology p) (a : ((ihom X.X₁).obj W).tateCohomology j) :
    (Rep.tateMap ((ihom.ev X.X₁).app W) (n + 1)).hom
        (cup X.X₁ ((ihom X.X₁).obj W) (p + 1) j (n + 1) (by omega) ((Rep.tateδ hX p).hom x) a)
      + ((p.negOnePow : ℤ) : k) • (Rep.tateMap ((ihom.ev X.X₃).app W) (n + 1)).hom
          (cup X.X₃ ((ihom X.X₃).obj W) p (j + 1) (n + 1) (by omega) x
            ((Rep.tateδ (dualSC_shortExact W hX s hs) j).hom a)) = 0 := by
  have hY := dualSC_shortExact W hX s hs
  have hR : (X.map (MonoidalCategory.tensorRight (dualSC W X).X₃)).ShortExact :=
    Rep.shortExact_map_tensorRight_of_splitting hX s hs _
  have hC : ((dualSC W X).map (MonoidalCategory.tensorLeft X.X₃)).ShortExact :=
    Rep.shortExact_map_tensorLeft_of_splitting hY (dualSection W hX s hs) (g_dualSection W hX s hs) _
  have P := Rep.tateMap_tateDelta_add_tateMap_tateDelta_eq_zero hX hY hR hC ((ihom.ev X.X₂).app W) ((ihom.ev X.X₁).app W)
    ((ihom.ev X.X₃).app W) (ev_compat_f W X) (ev_compat_g W X) n (cup X.X₃ ((ihom X.X₁).obj W) p j n h x a)
  refine Eq.trans ?_ P
  congr 1
  · exact (congrArg (fun t => (Rep.tateMap ((ihom.ev X.X₁).app W) (n + 1)).hom t)
      (hcup.delta_cup hX ((ihom X.X₁).obj W) hR p j n h x a)).symm
  · exact ((congrArg (fun t => (Rep.tateMap ((ihom.ev X.X₃).app W) (n + 1)).hom t)
      (hcup.cup_delta X.X₃ hY hC p j n h x a)).trans (map_smul _ _ _)).symm

theorem pair_cup' {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (hX : X.ShortExact)
    (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (W : Rep.{u} k G)
    (p j n m : ℤ) (h : p + j = n) (hm : n + 1 = m) (x : X.X₃.tateCohomology p) (a : ((ihom X.X₁).obj W).tateCohomology j) :
    (Rep.tateMap ((ihom.ev X.X₁).app W) m).hom
        (cup X.X₁ ((ihom X.X₁).obj W) (p + 1) j m (by omega) ((Rep.tateδ hX p).hom x) a)
      + ((p.negOnePow : ℤ) : k) • (Rep.tateMap ((ihom.ev X.X₃).app W) m).hom
          (cup X.X₃ ((ihom X.X₃).obj W) p (j + 1) m (by omega) x
            ((Rep.tateδ (dualSC_shortExact W hX s hs) j).hom a)) = 0 := by
  subst hm
  exact pair_cup hcup hX s hs W p j n h x a

def upSection (A : Rep.{u} k G) : A.dimShiftUpObj →ₗ[k] A.indBot :=
  (LinearMap.range (Rep.indBotι A).hom.toLinearMap).liftQ
    (LinearMap.id - (Rep.indBotι A).hom.toLinearMap ∘ₗ A.indBotr) (by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Representation.IntertwiningMap.toLinearMap_apply, Rep.indBotr_indBotIota]
      exact sub_self _)

theorem g_upSection (A : Rep.{u} k G) (x : A.dimShiftUpObj) : A.dimShiftUp.g.hom (upSection A x) = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (x - (Rep.indBotι A).hom (A.indBotr x)) = Submodule.Quotient.mk x
  rw [Submodule.Quotient.mk_sub, sub_eq_self, Submodule.Quotient.mk_eq_zero]
  exact ⟨A.indBotr x, rfl⟩

omit [Fintype G] in
theorem eps_smul_eps_smul {M : Type u} [AddCommGroup M] [Module k M] (p : ℤ) (v : M) :
    ((p.negOnePow : ℤ) : k) • ((p.negOnePow : ℤ) : k) • v = v := by
  rw [smul_smul, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]

omit [Fintype G] in
theorem eq_zero_of_eps_smul_eq_zero {M : Type u} [AddCommGroup M] [Module k M] (p : ℤ) (v : M)
    (h : ((p.negOnePow : ℤ) : k) • v = 0) : v = 0 := by
  rw [← eps_smul_eps_smul (k := k) p v, h, smul_zero]

theorem bijective_tateδ_dual_of_indBot (W : Rep.{u} k G) (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂)
    (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (A : Rep.{u} k G) (hA : X.X₂ = A.indBot) (j : ℤ) :
    Function.Bijective (Rep.tateδ (dualSC_shortExact W hX s hs) j).hom := by
  have h1 : ∀ i : ℤ, CategoryTheory.Limits.IsZero (((ihom X.X₂).obj W).tateCohomology i) := by
    rw [hA]
    exact fun i => Rep.isZero_tateCohomology_ihom_indBot A W i
  exact Rep.bijective_tateDelta_of_isZero _ j (h1 j) (h1 (j + 1))

end generic

end

end P2mS26FDpL
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_injective_cupEv_characterDual.P2mS26FDpL"

namespace P2mS26FDpL

variable {G : Type} [Group G] [Fintype G] {cup : Rep.TateCupFamily ℤ G}

def KerP (cup : Rep.TateCupFamily ℤ G) (p : ℤ) : Prop :=
  ∀ (M : Rep ℤ G) (q : ℤ) (h : p + q = -1) (x : M.tateCohomology p),
    (∀ a : ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology q,
      (Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom
        (cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) p q (-1) h x a) = 0) → x = 0

theorem base (hcup : Rep.IsTateCupProduct cup) : KerP cup (-1) := by
  intro M q h x hx
  obtain rfl : q = 0 := by omega
  have h0 : (fun x : M.tateCohomology (-1) =>
      ((Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom ∘ₗ
        cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1) 0 (-1) (add_zero (-1)) x :
          ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology 0 →ₗ[ℤ]
            (Rep.trivial ℤ G (AddCircle (1 : ℚ))).tateCohomology (-1))) x
      = (fun x : M.tateCohomology (-1) =>
      ((Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom ∘ₗ
        cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1) 0 (-1) (add_zero (-1)) x :
          ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology 0 →ₗ[ℤ]
            (Rep.trivial ℤ G (AddCircle (1 : ℚ))).tateCohomology (-1))) 0 := by
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.comp_apply, map_zero, LinearMap.zero_apply]
    exact hx a
  exact Rep.IsTateCupProduct.injective_cupEv_negOne_characterDual hcup M h0

theorem down (hcup : Rep.IsTateCupProduct cup) (p : ℤ) (ih : KerP cup (p + 1)) : KerP cup p := by
  intro M q h x hx
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  have hX := Rep.dimShiftDown_shortExact M
  refine (injective_iff_map_eq_zero (Rep.tateδ hX p).hom).1 (Rep.bijective_tateDelta_dimShiftDown M hX p).1 x ?_
  refine ih M.dimShiftDown.X₁ j (by omega) ((Rep.tateδ hX p).hom x) fun a => ?_
  have hx' : ∀ b, (Rep.tateMap ((ihom.ev M.dimShiftDown.X₃).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom
      (cup M.dimShiftDown.X₃ ((ihom M.dimShiftDown.X₃).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) p (j + 1) (-1) (by omega) x b) = 0 := hx
  have e := pair_cup' hcup hX M.indBotσ (Rep.indBotPi_indBotSigma M) (Rep.trivial ℤ G (AddCircle (1 : ℚ))) p j (-2) (-1) (by omega)
    (by norm_num) x a
  rw [hx' _, smul_zero, add_zero] at e
  exact e

theorem up (hcup : Rep.IsTateCupProduct cup) (p : ℤ) (ih : KerP cup p) : KerP cup (p + 1) := by
  intro N q h x hx
  have hX := Rep.dimShiftUp_shortExact N
  obtain ⟨x, rfl⟩ := (Rep.bijective_tateDelta_dimShiftUp N hX p).2 x
  have hδY := bijective_tateδ_dual_of_indBot (Rep.trivial ℤ G (AddCircle (1 : ℚ))) hX (upSection N) (g_upSection N) N rfl q
  suffices hx0 : x = 0 by rw [hx0]; exact map_zero _
  refine ih N.dimShiftUp.X₃ (q + 1) (by omega) x fun b => ?_
  obtain ⟨a, rfl⟩ := hδY.2 b
  have hx' : ∀ c, (Rep.tateMap ((ihom.ev N.dimShiftUp.X₁).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom
      (cup N.dimShiftUp.X₁ ((ihom N.dimShiftUp.X₁).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (p + 1) q (-1) (by omega)
        ((Rep.tateδ hX p).hom x) c) = 0 := hx
  have e := pair_cup' hcup hX (upSection N) (g_upSection N) (Rep.trivial ℤ G (AddCircle (1 : ℚ))) p q (-2) (-1) (by omega)
    (by norm_num) x a
  rw [hx' _, zero_add] at e
  exact eq_zero_of_eps_smul_eq_zero p _ e

theorem all (hcup : Rep.IsTateCupProduct cup) (p : ℤ) : KerP cup p :=
  Int.inductionOn' p (-1) (base hcup) (fun k _ hk => up hcup k hk)
    (fun k _ hk => down hcup (k - 1) (by rwa [sub_add_cancel]))

end P2mS26FDpL
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_injective_cupEv_characterDual.P2mS26FDpL"

open P2mS26FDpL in
theorem solution {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup) (M : Rep ℤ G) (p q : ℤ) (h : p + q = -1) :
    Function.Injective (fun x : M.tateCohomology p =>
      ((Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom ∘ₗ
        cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) p q (-1) h x :
          ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology q →ₗ[ℤ]
            (Rep.trivial ℤ G (AddCircle (1 : ℚ))).tateCohomology (-1))) := by
  intro x₁ x₂ hx12
  rw [← sub_eq_zero]
  refine all hcup p M q h (x₁ - x₂) fun a => ?_
  have h1 := LinearMap.congr_fun hx12 a
  simp only [LinearMap.coe_comp, Function.comp_apply] at h1
  change (Rep.tateMap _ (-1)).hom (cup M _ p q (-1) h (x₁ - x₂) a) = 0
  rw [map_sub, LinearMap.sub_apply, map_sub]
  exact sub_eq_zero.2 h1

end S_Rep_IsTateCupProduct_injective_cupEv_characterDual
end P2MW
export P2MW.S_Rep_IsTateCupProduct_injective_cupEv_characterDual (solution)

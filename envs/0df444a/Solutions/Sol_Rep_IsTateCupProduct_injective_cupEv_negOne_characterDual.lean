-- Prove2me | solution 1 for Rep.IsTateCupProduct.injective_cupEv_negOne_characterDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/46dbe193-d9ae-5c24-a7d2-fbc37a16676c

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Theorems.Thm_Rep_IsTateCupProduct_cup_neg_one_mk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_IsTateCupProduct_injective_cupEv_negOne_characterDual

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

attribute [local instance 2000] Rep.hV2 Rep.hV1

namespace P2mS26FD0L

section generic
variable {k G : Type u} [CommRing k] [Group G]

lemma ker_trivial_eq_bot (V : Type u) [AddCommGroup V] [Module k V] :
    Representation.Coinvariants.ker (Representation.trivial k G V) = ⊥ := by
  rw [Representation.Coinvariants.ker, Submodule.span_eq_bot]
  rintro _ ⟨⟨g, v⟩, rfl⟩
  simp

lemma mk_trivial_eq_zero_iff (V : Type u) [AddCommGroup V] [Module k V] (v : V) :
    Representation.Coinvariants.mk (Representation.trivial k G V) v = 0 ↔ v = 0 := by
  rw [Representation.Coinvariants.mk_eq_zero, ker_trivial_eq_bot, Submodule.mem_bot]

def ofD (M W : Rep.{u} k G) (f : (ihom M).obj W) : (M : Type u) →ₗ[k] W := f

def toD (M W : Rep.{u} k G) (f : (M : Type u) →ₗ[k] W) : (ihom M).obj W := f

@[scoped simp] lemma ofD_toD (M W : Rep.{u} k G) (f : (M : Type u) →ₗ[k] W) : ofD M W (toD M W f) = f := rfl

lemma ofD_ρ (M W : Rep.{u} k G) (g : G) (f : (ihom M).obj W) :
    ofD M W (((ihom M).obj W).ρ g f) = W.ρ g ∘ₗ ofD M W f ∘ₗ M.ρ g⁻¹ :=
  Rep.ihom_obj_ρ_apply (A := M) (B := W) g (ofD M W f)

lemma ev_tmul (M W : Rep.{u} k G) (m : M) (f : (ihom M).obj W) :
    ((ihom.ev M).app W).hom (m ⊗ₜ[k] f : (M ⊗ (ihom M).obj W : Rep.{u} k G)) = ofD M W f m := by
  change ((ihom.ev M).app W).hom.toLinearMap (m ⊗ₜ[k] f) = ofD M W f m
  rw [Rep.ihom_ev_app_hom]
  rfl

def evD (M W : Rep.{u} k G) (m : M) : ((ihom M).obj W : Type u) →+ W where
  toFun f := ofD M W f m
  map_zero' := rfl
  map_add' _ _ := rfl

variable [Fintype G]

lemma ofD_norm_apply (M W : Rep.{u} k G) (f : (ihom M).obj W) (m : M) :
    ofD M W (((ihom M).obj W).ρ.norm f) m = ∑ g, W.ρ g (ofD M W f (M.ρ g⁻¹ m)) := by
  rw [Representation.norm, LinearMap.coe_sum, Finset.sum_apply]
  change evD M W m (∑ g, ((ihom M).obj W).ρ g f) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  change ofD M W (((ihom M).obj W).ρ g f) m = _
  rw [ofD_ρ]
  rfl

lemma norm_tmul_of_mem_invariants (M B : Rep.{u} k G) (m : M) (b : B) (hb : b ∈ B.ρ.invariants) :
    (M ⊗ B).ρ.norm (m ⊗ₜ[k] b) = M.ρ.norm m ⊗ₜ[k] b := by
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun g _ => ?_
  change (M.ρ.tprod B.ρ) g (m ⊗ₜ[k] b) = _
  rw [Representation.tprod_apply, TensorProduct.map_tmul, (Representation.mem_invariants _ _).1 hb g]

lemma norm_eq_zero_of_tateHneg1 (M : Rep.{u} k G) (x : M.tateHneg1) (m : M)
    (hx : (x : M.ρ.Coinvariants) = Representation.Coinvariants.mk M.ρ m) : M.ρ.norm m = 0 := by
  have h : M.ρ.normBar (x : M.ρ.Coinvariants) = 0 := x.2
  rw [hx, Representation.normBar_mk] at h
  exact congrArg Subtype.val h

def mkHneg1 (A : Rep.{u} k G) (m : A) (hm : A.ρ.norm m = 0) : A.tateHneg1 :=
  ⟨Representation.Coinvariants.mk A.ρ m, by
    change A.ρ.normBar (Representation.Coinvariants.mk A.ρ m) = 0
    exact Subtype.ext (by rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply]; exact hm)⟩

lemma tateH0_mk_eq_zero (A : Rep.{u} k G) (f : A.ρ.invariants) (h : A) (hh : A.ρ.norm h = (f : A)) :
    (Submodule.Quotient.mk f : A.tateH0) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 ⟨Representation.Coinvariants.mk A.ρ h,
    Subtype.ext (by rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply]; exact hh)⟩

noncomputable def zOf (M B : Rep.{u} k G) (x : M.tateHneg1) (m : M)
    (hx : (x : M.ρ.Coinvariants) = Representation.Coinvariants.mk M.ρ m) (b : B.ρ.invariants) : (M ⊗ B).tateHneg1 :=
  ⟨Representation.Coinvariants.mk (M ⊗ B).ρ (m ⊗ₜ[k] (b : B)), by
    change (M ⊗ B).ρ.normBar (Representation.Coinvariants.mk (M ⊗ B).ρ (m ⊗ₜ[k] (b : B))) = 0
    apply Subtype.ext
    rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply]
    change (M ⊗ B).ρ.norm (m ⊗ₜ[k] (b : B)) = 0
    rw [norm_tmul_of_mem_invariants M B m b b.2, norm_eq_zero_of_tateHneg1 M x m hx, TensorProduct.zero_tmul]⟩

lemma apply_eq_zero_of_pairing_eq_zero {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup)
    (M : Rep.{u} k G) (V : Type u) [AddCommGroup V] [Module k V]
    (x : M.tateHneg1) (m : M) (hx : (x : M.ρ.Coinvariants) = Representation.Coinvariants.mk M.ρ m)
    (b : ((ihom M).obj (Rep.trivial k G V)).ρ.invariants)
    (h : (Rep.tateMap ((ihom.ev M).app (Rep.trivial k G V)) (-1)).hom
        (cup M ((ihom M).obj (Rep.trivial k G V)) (-1) 0 (-1) (add_zero (-1))
          (show M.tateCohomology (-1) from x) (Submodule.Quotient.mk b)) = 0) :
    ofD M (Rep.trivial k G V) b m = 0 := by
  rw [hcup.cup_neg_one_mk M _ x m hx b (zOf M _ x m hx b) rfl] at h
  have h1 : (_ : (Rep.trivial k G V).ρ.Coinvariants) = _ := congrArg Subtype.val h
  change Representation.Coinvariants.mk _ (((ihom.ev M).app (Rep.trivial k G V)).hom
    (m ⊗ₜ[k] (b : (ihom M).obj (Rep.trivial k G V)) : (M ⊗ (ihom M).obj (Rep.trivial k G V) : Rep.{u} k G))) = 0 at h1
  rw [ev_tmul] at h1
  exact (mk_trivial_eq_zero_iff V _).1 h1

end generic

section intRep
variable {G : Type} [Group G]

def linOfAdd (M : Rep ℤ G) (W : Type) [AddCommGroup W] [Module ℤ W] (h : (M : Type) →+ W) :
    (M : Type) →ₗ[ℤ] W where
  toFun := h
  map_add' := h.map_add
  map_smul' z m := (congrArg h (int_smul_eq_zsmul M.hV2 z m)).trans
    ((map_zsmul h z m).trans (int_smul_eq_zsmul _ z (h m)).symm)

@[scoped simp] lemma linOfAdd_apply (M : Rep ℤ G) (W : Type) [AddCommGroup W] [Module ℤ W] (h : (M : Type) →+ W) (m : M) :
    linOfAdd M W h m = h m := rfl

end intRep

end P2mS26FD0L
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_injective_cupEv_negOne_characterDual.P2mS26FD0L"

open P2mS26FD0L in
theorem solution {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup) (M : Rep ℤ G) :
    Function.Injective (fun x : M.tateCohomology (-1) =>
      ((Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom ∘ₗ
        cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1) 0 (-1) (add_zero (-1)) x :
          ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology 0 →ₗ[ℤ]
            (Rep.trivial ℤ G (AddCircle (1 : ℚ))).tateCohomology (-1))) := by

  have key : ∀ x : M.tateHneg1,
      (∀ b : ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).ρ.invariants,
        (Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom
          (cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1) 0 (-1) (add_zero (-1))
            (show M.tateCohomology (-1) from x) (Submodule.Quotient.mk b)) = 0) → x = 0 := by
    intro x hx
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (x : M.ρ.Coinvariants)
    have hm' : (x : M.ρ.Coinvariants) = Representation.Coinvariants.mk M.ρ m := hm.symm
    by_contra hne
    have hne' : (x : M.ρ.Coinvariants) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne'
    let b₀ : (M : Type) →ₗ[ℤ] AddCircle (1 : ℚ) := linOfAdd M (AddCircle (1 : ℚ))
      (AddMonoidHom.comp (c : M.ρ.Coinvariants →+ AddCircle (1 : ℚ)) (Representation.Coinvariants.mk M.ρ).toAddMonoidHom)
    have hb₀v : ∀ v : M, b₀ v = c (Representation.Coinvariants.mk M.ρ v) := fun v => rfl
    have hb₀ : ∀ (g : G) (v : M), b₀ (M.ρ g v) = b₀ v := fun g v => by
      rw [hb₀v, hb₀v]
      congr 1
      exact (Representation.Coinvariants.mk_eq_iff _).2 (Representation.Coinvariants.sub_mem_ker g v)
    have hρ : ∀ g : G, ofD M _ (((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).ρ g
        (toD M (Rep.trivial ℤ G (AddCircle (1 : ℚ))) b₀)) = b₀ := fun g => by
      rw [ofD_ρ, ofD_toD]
      exact LinearMap.ext fun v => hb₀ g⁻¹ v
    have hbinv : toD M (Rep.trivial ℤ G (AddCircle (1 : ℚ))) b₀
        ∈ ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).ρ.invariants :=
      (Representation.mem_invariants _ _).2 fun g => congrArg (toD M (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (hρ g)
    have h0 := apply_eq_zero_of_pairing_eq_zero hcup M (AddCircle (1 : ℚ)) x m hm' ⟨_, hbinv⟩ (hx ⟨_, hbinv⟩)
    refine hc ?_
    rw [hm', ← hb₀v]
    exact h0
  intro x₁ x₂ h
  rw [← sub_eq_zero]
  refine key (x₁ - x₂) fun b => ?_
  have h1 := LinearMap.congr_fun h (Submodule.Quotient.mk b)
  simp only [LinearMap.coe_comp, Function.comp_apply] at h1
  change (Rep.tateMap _ (-1)).hom (cup M _ (-1) 0 (-1) _ (x₁ - x₂) (Submodule.Quotient.mk b)) = 0
  rw [map_sub, LinearMap.sub_apply, map_sub]
  exact sub_eq_zero.2 h1

end S_Rep_IsTateCupProduct_injective_cupEv_negOne_characterDual
end P2MW
export P2MW.S_Rep_IsTateCupProduct_injective_cupEv_negOne_characterDual (solution)

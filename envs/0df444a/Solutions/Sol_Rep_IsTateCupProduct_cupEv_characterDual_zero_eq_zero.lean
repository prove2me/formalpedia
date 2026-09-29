-- Prove2me | solution 1 for Rep.IsTateCupProduct.cupEv_characterDual_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0cbd32ba-cde5-5a9b-99a6-34800b1cbc58

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

namespace P2MW.S_Rep_IsTateCupProduct_cupEv_characterDual_zero_eq_zero

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

attribute [local instance 2000] Rep.hV2 Rep.hV1

namespace P2mS26FD0R

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

end P2mS26FD0R
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_cupEv_characterDual_zero_eq_zero.P2mS26FD0R"

namespace P2mS26FD0R

lemma exists_comp_eq (V : Type) [AddCommGroup V] (N : V →+ V) (f : V →+ AddCircle (1 : ℚ))
    (hf : ∀ v, N v = 0 → f v = 0) : ∃ h : V →+ AddCircle (1 : ℚ), ∀ v, h (N v) = f v := by
  let N' : V →ₗ[ℤ] V := N.toIntLinearMap
  let f' : V →ₗ[ℤ] AddCircle (1 : ℚ) := f.toIntLinearMap
  have hle : LinearMap.ker N' ≤ LinearMap.ker f' := fun v hv => hf v hv
  let ψ : LinearMap.range N' →ₗ[ℤ] AddCircle (1 : ℚ) :=
    (LinearMap.ker N').liftQ f' hle ∘ₗ N'.quotKerEquivRange.symm.toLinearMap
  have hψ : ∀ v, ψ ⟨N' v, LinearMap.mem_range_self N' v⟩ = f v := fun v => by
    change (LinearMap.ker N').liftQ f' hle (N'.quotKerEquivRange.symm ⟨N' v, _⟩) = f v
    rw [LinearMap.quotKerEquivRange_symm_apply_image N' v, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  obtain ⟨c, hc⟩ := CharacterModule.dual_surjective_of_injective (LinearMap.range N').subtype
    (LinearMap.range N').injective_subtype ψ.toAddMonoidHom
  refine ⟨c, fun v => ?_⟩
  have h1 := DFunLike.congr_fun hc ⟨N' v, LinearMap.mem_range_self N' v⟩
  rw [CharacterModule.dual_apply] at h1
  exact h1.trans (hψ v)

end P2mS26FD0R
p2m_reactivate "P2MW.S_Rep_IsTateCupProduct_cupEv_characterDual_zero_eq_zero.P2mS26FD0R"

open P2mS26FD0R in
theorem solution {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup) (M : Rep ℤ G)
    (a : ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology 0)
    (ha : ∀ x : M.tateCohomology (-1),
      (Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom
        (cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1) 0 (-1) (add_zero (-1)) x a) = 0) :
    a = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a

  have hker : ∀ m : M, M.ρ.norm m = 0 → ofD M (Rep.trivial ℤ G (AddCircle (1 : ℚ))) f m = 0 := fun m hm =>
    apply_eq_zero_of_pairing_eq_zero hcup M (AddCircle (1 : ℚ)) (mkHneg1 M m hm) m rfl f (ha _)

  obtain ⟨h, hh⟩ := exists_comp_eq M M.ρ.norm.toAddMonoidHom
    (ofD M (Rep.trivial ℤ G (AddCircle (1 : ℚ))) f).toAddMonoidHom hker

  refine tateH0_mk_eq_zero _ f (toD M (Rep.trivial ℤ G (AddCircle (1 : ℚ))) (linOfAdd M _ h)) ?_
  have key : ofD M _ (((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).ρ.norm
      (toD M (Rep.trivial ℤ G (AddCircle (1 : ℚ))) (linOfAdd M _ h))) = ofD M (Rep.trivial ℤ G (AddCircle (1 : ℚ))) f := by
    refine LinearMap.ext fun m => ?_
    rw [ofD_norm_apply]
    change ∑ g, h (M.ρ g⁻¹ m) = ofD M (Rep.trivial ℤ G (AddCircle (1 : ℚ))) f m
    rw [← map_sum]
    refine (congrArg h ?_).trans (hh m)
    change ∑ g, M.ρ g⁻¹ m = M.ρ.norm m
    rw [Representation.norm, LinearMap.coe_sum, Finset.sum_apply]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl
  exact congrArg (toD M (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) key

end S_Rep_IsTateCupProduct_cupEv_characterDual_zero_eq_zero
end P2MW
export P2MW.S_Rep_IsTateCupProduct_cupEv_characterDual_zero_eq_zero (solution)

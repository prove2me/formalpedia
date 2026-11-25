-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.not_mono_biprod_desc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:41.312973+00:00
-- url     : https://prove2.me/submissions/606631e0-eab1-40d3-a833-99f64009d5ae

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_zero_of_coord_last_eq_zero
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_mono_iff_injective
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_app_val
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_isZero_interval
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val_of_mem


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {a c c' d : Fin n} (hac : a ≤ c) (hac' : a ≤ c') (hcd : c ≤ d)
    (hcd' : c' ≤ d) (f : interval k c d ⟶ interval k a d) (g : interval k c' d ⟶ interval k a d) :
    ¬ Mono (biprod.desc f g) := by
  intro hmono
  have hinj := (FGModuleCat.mono_iff_injective ((biprod.desc f g).app d)).1
    ((NatTrans.mono_iff_mono_app _).1 hmono d)
  -- component identities at the vertex `d`
  have hinl_desc : ∀ y, ((biprod.desc f g).app d).hom.hom
      (((biprod.inl : interval k c d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) =
      (f.app d).hom.hom y := fun y => by
    change ((biprod.inl ≫ biprod.desc f g).app d).hom.hom y = _
    rw [biprod.inl_desc]
  have hinr_desc : ∀ y, ((biprod.desc f g).app d).hom.hom
      (((biprod.inr : interval k c' d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) =
      (g.app d).hom.hom y := fun y => by
    change ((biprod.inr ≫ biprod.desc f g).app d).hom.hom y = _
    rw [biprod.inr_desc]
  have hinl_fst : ∀ y, ((biprod.fst : interval k c d ⊞ interval k c' d ⟶ interval k c d).app d).hom.hom
      (((biprod.inl : interval k c d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) = y :=
    fun y => by
      change ((biprod.inl ≫ biprod.fst : interval k c d ⟶ interval k c d).app d).hom.hom y = y
      rw [biprod.inl_fst]
      rfl
  have hinr_fst : ∀ y, ((biprod.fst : interval k c d ⊞ interval k c' d ⟶ interval k c d).app d).hom.hom
      (((biprod.inr : interval k c' d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) = 0 :=
    fun y => by
      change ((biprod.inr ≫ biprod.fst : interval k c' d ⟶ interval k c d).app d).hom.hom y = 0
      rw [biprod.inr_fst]
      rfl
  -- the vector `(coord g d) • u - (coord f d) • u'` at the vertex `d` is in the kernel
  set x : (interval k c d ⊞ interval k c' d).obj d :=
    ((biprod.inl : interval k c d ⟶ _).app d).hom.hom ((coord g d) • unit k c d d) -
      ((biprod.inr : interval k c' d ⟶ _).app d).hom.hom ((coord f d) • unit k c' d d) with hx
  have hfx : ((biprod.desc f g).app d).hom.hom x = 0 := by
    rw [hx, map_sub, hinl_desc, hinr_desc, sub_eq_zero]
    apply Subtype.ext
    rw [app_val, app_val, Submodule.coe_smul, Submodule.coe_smul, unit_val_of_mem k ⟨hcd, le_rfl⟩,
      unit_val_of_mem k ⟨hcd', le_rfl⟩, smul_eq_mul, smul_eq_mul, mul_one, mul_one, mul_comm]
  have hx0 : x = 0 := hinj (by rw [hfx, map_zero])
  -- hence `coord g d = 0`
  have hg : coord g d = 0 := by
    have := congrArg (fun y => (((biprod.fst : interval k c d ⊞ interval k c' d ⟶ interval k c d).app d).hom.hom y : intervalSpace k c d d).1) hx0
    simp only [hx, map_sub, hinl_fst, hinr_fst, sub_zero, map_zero] at this
    rw [Submodule.coe_smul, unit_val_of_mem k ⟨hcd, le_rfl⟩, smul_eq_mul, mul_one] at this
    exact this
  -- so `g = 0`; then `f` is a mono `M_{c,d} ⟶ M_{a,d}` restricted from `desc`, fine, but the
  -- same argument with `snd` gives `coord f d = 0` and `f = 0`
  have hinl_snd : ∀ y, ((biprod.snd : interval k c d ⊞ interval k c' d ⟶ interval k c' d).app d).hom.hom
      (((biprod.inl : interval k c d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) = 0 :=
    fun y => by
      change ((biprod.inl ≫ biprod.snd : interval k c d ⟶ interval k c' d).app d).hom.hom y = 0
      rw [biprod.inl_snd]
      rfl
  have hinr_snd : ∀ y, ((biprod.snd : interval k c d ⊞ interval k c' d ⟶ interval k c' d).app d).hom.hom
      (((biprod.inr : interval k c' d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) = y :=
    fun y => by
      change ((biprod.inr ≫ biprod.snd : interval k c' d ⟶ interval k c' d).app d).hom.hom y = y
      rw [biprod.inr_snd]
      rfl
  have hf : coord f d = 0 := by
    have := congrArg (fun y => (((biprod.snd : interval k c d ⊞ interval k c' d ⟶ interval k c' d).app d).hom.hom y : intervalSpace k c' d d).1) hx0
    simp only [hx, map_sub, hinl_snd, hinr_snd, zero_sub, map_zero, Submodule.coe_neg,
      Submodule.coe_zero, neg_eq_zero, Submodule.coe_smul, smul_eq_mul] at this
    rwa [unit_val_of_mem k ⟨hcd', le_rfl⟩, mul_one] at this
  have hf0 : f = 0 := eq_zero_of_coord_last_eq_zero hac hcd f hf
  have hg0 : g = 0 := eq_zero_of_coord_last_eq_zero hac' hcd' g hg
  -- a monomorphism that is zero has zero source
  have hdesc0 : biprod.desc f g = 0 := by
    rw [hf0, hg0]
    apply biprod.hom_ext' <;> simp
  rw [hdesc0] at hmono
  have hz : IsZero (interval k c d ⊞ interval k c' d) := by
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (0 : interval k c d ⊞ interval k c' d ⟶ interval k a d),
      zero_comp, comp_zero]
  exact not_isZero_interval hcd
    (IsZero.of_mono (biprod.inl : interval k c d ⟶ interval k c d ⊞ interval k c' d) hz)
end PretorsionImageClosed.LinearQuiver

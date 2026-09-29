-- Prove2me | solution 1 for Rep.IsTateCupProduct.cup_mk_right_eq_tateMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/00b64187-b5b5-5d91-926e-eee035616bf1

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Theorems.Thm_groupCohomology_d_cochainCup_apply
import Theorems.Thm_groupCohomology_IsGradedCupProduct_cup_delta
import Theorems.Thm_groupCohomology_exists_isGradedCupProduct
import Theorems.Thm_Rep_dimShiftDown_shortExact
import Theorems.Thm_Rep_dimShiftUp_shortExact
import Theorems.Thm_Rep_bijective_tateDelta_of_isZero
import Theorems.Thm_Rep_bijective_tateDelta_dimShiftUp
import Theorems.Thm_Rep_isZero_tateCohomology_indBot_tensor
import Theorems.Thm_Rep_isZero_tateCohomology_tensor_indBot
import Theorems.Thm_Rep_shortExact_dimShiftDown_map_tensorRight
import Theorems.Thm_Rep_shortExact_dimShiftDown_map_tensorLeft
import Theorems.Thm_Rep_shortExact_map_tensorRight_of_splitting
import Theorems.Thm_Rep_indBotr_indBotIota
import Theorems.Thm_Rep_tateDelta_naturality
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_IsTateCupProduct_cup_mk_right_eq_tateMap

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"
open groupCohomology

namespace P2mS26H0c

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

theorem d_iCocycles (A : Rep.{u} k G) (n : ℕ) (x : cocycles A n) :
    (inhomogeneousCochains.d A n).hom ((iCocycles A n).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) ((inhomogeneousCochains A).iCycles_d n (n + 1))
  simpa [ModuleCat.hom_comp] using this

theorem d_cup_eq_zero (A B : Rep.{u} k G) (p q : ℕ) (x : cocycles A p) (y : cocycles B q) :
    (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom
      (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) = 0 := by
  funext σ
  rw [groupCohomology.d_cochainCup_apply, d_iCocycles, d_iCocycles, map_zero, map_zero, LinearMap.zero_apply,
    Pi.zero_apply, Pi.zero_apply, smul_zero, add_zero]

theorem π_surjective (A : Rep.{u} k G) (n : ℕ) : Function.Surjective (groupCohomology.π A n).hom :=
  (ModuleCat.epi_iff_surjective ((inhomogeneousCochains A).homologyπ n)).1 inferInstance

theorem iCocycles_injective (A : Rep.{u} k G) (n : ℕ) : Function.Injective (iCocycles A n).hom :=
  (ModuleCat.mono_iff_injective (iCocycles A n)).1 inferInstance

theorem i_cocyclesMk {A : Rep.{u} k G} {n : ℕ} (x : (Fin n → G) → A) (h) :
    (iCocycles A n).hom (cocyclesMk x h) = x :=
  iCocycles_mk x h

theorem π_map_hom {A A' : Rep.{u} k G} (φ : A ⟶ A') (n : ℕ) (z : cocycles A n) :
    (groupCohomology.map (MonoidHom.id G) φ n).hom ((groupCohomology.π A n).hom z)
      = (groupCohomology.π A' n).hom ((cocyclesMap (MonoidHom.id G) φ n).hom z) := by
  have := congrArg (fun ψ => ψ.hom z) (groupCohomology.π_map (MonoidHom.id G) φ n)
  simpa [ModuleCat.hom_comp] using this

theorem i_cocyclesMap {A A' : Rep.{u} k G} (φ : A ⟶ A') (n : ℕ) (z : cocycles A n) :
    (iCocycles A' n).hom ((cocyclesMap (MonoidHom.id G) φ n).hom z)
      = ((cochainsMap (MonoidHom.id G) φ).f n).hom ((iCocycles A n).hom z) := by
  have := congrArg (fun ψ => ψ.hom z) (HomologicalComplex.cyclesMap_i (cochainsMap (MonoidHom.id G) φ) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

theorem cochainsMap_f_apply {A A' : Rep.{u} k G} (φ : A ⟶ A') (n : ℕ) (x : (Fin n → G) → A) (σ : Fin n → G) :
    ((cochainsMap (MonoidHom.id G) φ).f n).hom x σ = φ.hom (x σ) := by
  rw [cochainsMap_f_hom]
  rfl

def tmulRight (M B : Rep.{u} k G) (b : B.ρ.invariants) : M ⟶ M ⊗ B :=
  Rep.ofHom ⟨(TensorProduct.mk k M B).flip (b : B), fun g => LinearMap.ext fun m => by
    change (M.ρ g m) ⊗ₜ[k] (b : B) = (M.ρ.tprod B.ρ) g (m ⊗ₜ[k] (b : B))
    rw [Representation.tprod_apply, TensorProduct.map_tmul, b.2 g]⟩

theorem tmulRight_apply (M B : Rep.{u} k G) (b : B.ρ.invariants) (m : M) :
    (tmulRight M B b).hom m = m ⊗ₜ[k] (b : B) := rfl

def tmulRightNat (B : Rep.{u} k G) (b : B.ρ.invariants) (X : ShortComplex (Rep.{u} k G)) :
    X ⟶ X.map (MonoidalCategory.tensorRight B) where
  τ₁ := tmulRight X.X₁ B b
  τ₂ := tmulRight X.X₂ B b
  τ₃ := tmulRight X.X₃ B b
  comm₁₂ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  comm₂₃ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

theorem key (A B : Rep.{u} k G) (b : B.ρ.invariants)
    (cupg : GradedCupFamily A B) (hg : IsGradedCupProduct A B cupg) (z : cocycles A 1) :
    cupg 1 0 ((groupCohomology.π A 1).hom z) ((H0Iso B).inv b)
      = (groupCohomology.map (MonoidHom.id G) (tmulRight A B b) 1).hom ((groupCohomology.π A 1).hom z) := by
  have e : (H0Iso B).inv b = (groupCohomology.π B 0).hom ((cocyclesIso₀ B).inv b) := rfl
  have i0 : (iCocycles B 0).hom ((cocyclesIso₀ B).inv b) = (cochainsIso₀ B).inv (b : B) := by
    simp only [cocyclesIso₀_inv_comp_iCocycles_apply]
    rfl
  rw [e, hg.compat 1 0 z _ (d_cup_eq_zero A B 1 0 z _), π_map_hom]
  congr 1
  apply iCocycles_injective
  rw [i_cocyclesMk, i_cocyclesMap]
  funext σ
  rw [cochainsMap_f_apply, cochainCup_apply, i0, tmulRight_apply]
  have h1 : (cochainsIso₀ B).inv (b : B) (cochainCupSnd 1 0 σ) = b := by
    simp [cochainsIso₀]
  have h3 : cochainCupFst 1 0 σ = σ := funext fun i => congrArg σ (Fin.ext (by simp))
  rw [h1, b.2, h3]

variable [Fintype G]

theorem natAt {X Y : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (hY : Y.ShortExact) (τ : X ⟶ Y) (n : ℤ)
    (y : X.X₃.tateCohomology n) :
    (Rep.tateMap τ.τ₁ (n + 1)).hom ((Rep.tateδ hX n).hom y) = (Rep.tateδ hY n).hom ((Rep.tateMap τ.τ₃ n).hom y) := by
  have := congrArg (fun f => f.hom y) (Rep.tateDelta_naturality hX hY τ n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this

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

theorem shortExact_dimShiftUp_map_tensorRight (A B : Rep.{u} k G) :
    (A.dimShiftUp.map (MonoidalCategory.tensorRight B)).ShortExact :=
  Rep.shortExact_map_tensorRight_of_splitting (Rep.dimShiftUp_shortExact A) (upSection A) (g_upSection A) B

end

end P2mS26H0c

open P2mS26H0c in
theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (b : B.ρ.invariants) (ψ : A ⟶ A ⊗ B) (hψ : ∀ a : A, ψ.hom a = a ⊗ₜ[k] (b : B))
    (p : ℤ) (x : A.tateCohomology p) :
    cup A B p 0 p (add_zero p) x (Submodule.Quotient.mk b : B.tateH0) = (Rep.tateMap ψ p).hom x := by
  obtain rfl : ψ = tmulRight A B b :=
    Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a => hψ a))
  clear hψ
  revert A x

  have base : ∀ (A : Rep.{u} k G) (x : A.tateCohomology 1),
      cup A B 1 0 1 (add_zero 1) x (Submodule.Quotient.mk b : B.tateH0) = (Rep.tateMap (tmulRight A B b) 1).hom x := by
    intro A x
    obtain ⟨z, rfl⟩ := π_surjective A 1 x
    have hX := Rep.dimShiftDown_shortExact B
    have hAX := Rep.shortExact_dimShiftDown_map_tensorLeft A B
    refine (Rep.bijective_tateDelta_of_isZero hAX 1 (Rep.isZero_tateCohomology_tensor_indBot A B 1)
      (Rep.isZero_tateCohomology_tensor_indBot A B (1 + 1))).1 ?_
    refine (hcup.cup_delta A hX hAX 1 0 1 (add_zero 1) _ _).trans ?_
    rw [Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_smul, one_smul]
    obtain ⟨cupg₁, hg₁⟩ := groupCohomology.exists_isGradedCupProduct A B.dimShiftDown.X₁
    obtain ⟨cupg₃, hg₃⟩ := groupCohomology.exists_isGradedCupProduct A B
    have e2 := hcup.cup_ofNat_succ A B.dimShiftDown.X₁ cupg₁ hg₁ 0 0 ((groupCohomology.π A 1).hom z)
      ((Rep.tateδ hX 0).hom (Submodule.Quotient.mk b : B.tateH0))
    have e3 := groupCohomology.IsGradedCupProduct.cup_delta A hX hAX cupg₁ hg₁ cupg₃ hg₃ 1 0
      ((groupCohomology.π A 1).hom z) ((H0Iso B).inv b)
    rw [pow_one, neg_smul, one_smul] at e3
    exact (congrArg Neg.neg e2).trans (e3.symm.trans
      (congrArg (groupCohomology.δ hAX (1 + 0) (1 + 0 + 1) rfl).hom (key A B b cupg₃ hg₃ z)))

  have down : ∀ p : ℤ,
      (∀ (A : Rep.{u} k G) (x : A.tateCohomology (p + 1)),
        cup A B (p + 1) 0 (p + 1) (add_zero (p + 1)) x (Submodule.Quotient.mk b : B.tateH0)
          = (Rep.tateMap (tmulRight A B b) (p + 1)).hom x) →
      ∀ (A : Rep.{u} k G) (x : A.tateCohomology p),
        cup A B p 0 p (add_zero p) x (Submodule.Quotient.mk b : B.tateH0) = (Rep.tateMap (tmulRight A B b) p).hom x := by
    intro p ih A x
    have hX := Rep.dimShiftDown_shortExact A
    have hXB := Rep.shortExact_dimShiftDown_map_tensorRight A B
    refine (Rep.bijective_tateDelta_of_isZero hXB p (Rep.isZero_tateCohomology_indBot_tensor A B p)
      (Rep.isZero_tateCohomology_indBot_tensor A B (p + 1))).1 ?_
    exact (hcup.delta_cup hX B hXB p 0 p (add_zero p) x (Submodule.Quotient.mk b : B.tateH0)).trans
      ((ih A.dimShiftDown.X₁ ((Rep.tateδ hX p).hom x)).trans (natAt hX hXB (tmulRightNat B b A.dimShiftDown) p x))

  have up : ∀ p : ℤ,
      (∀ (A : Rep.{u} k G) (x : A.tateCohomology p),
        cup A B p 0 p (add_zero p) x (Submodule.Quotient.mk b : B.tateH0) = (Rep.tateMap (tmulRight A B b) p).hom x) →
      ∀ (A : Rep.{u} k G) (x : A.tateCohomology (p + 1)),
        cup A B (p + 1) 0 (p + 1) (add_zero (p + 1)) x (Submodule.Quotient.mk b : B.tateH0)
          = (Rep.tateMap (tmulRight A B b) (p + 1)).hom x := by
    intro p ih A x
    have hX := Rep.dimShiftUp_shortExact A
    have hXB := shortExact_dimShiftUp_map_tensorRight A B
    obtain ⟨y, rfl⟩ := (Rep.bijective_tateDelta_dimShiftUp A hX p).2 x
    exact (hcup.delta_cup hX B hXB p 0 p (add_zero p) y (Submodule.Quotient.mk b : B.tateH0)).symm.trans
      ((congrArg (Rep.tateδ hXB p).hom (ih A.dimShiftUp.X₃ y)).trans
        (natAt hX hXB (tmulRightNat B b A.dimShiftUp) p y).symm)

  have pos : ∀ j : ℕ, ∀ (A : Rep.{u} k G) (x : A.tateCohomology (1 + j)),
      cup A B (1 + j) 0 (1 + j) (add_zero _) x (Submodule.Quotient.mk b : B.tateH0)
        = (Rep.tateMap (tmulRight A B b) (1 + j)).hom x := by
    intro j
    induction j with
    | zero => rw [Nat.cast_zero, add_zero]; exact base
    | succ j ih =>
      have := up _ ih
      rwa [show (1 + (j : ℤ) + 1) = 1 + ((j + 1 : ℕ) : ℤ) by push_cast; ring] at this
  have neg : ∀ j : ℕ, ∀ (A : Rep.{u} k G) (x : A.tateCohomology (1 - j)),
      cup A B (1 - j) 0 (1 - j) (add_zero _) x (Submodule.Quotient.mk b : B.tateH0)
        = (Rep.tateMap (tmulRight A B b) (1 - j)).hom x := by
    intro j
    induction j with
    | zero => rw [Nat.cast_zero, sub_zero]; exact base
    | succ j ih =>
      refine down _ ?_
      rwa [show (1 - ((j + 1 : ℕ) : ℤ) + 1) = 1 - (j : ℤ) by push_cast; ring]
  intro A x
  rcases le_or_gt 1 p with hp | hp
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, p = 1 + j := ⟨(p - 1).toNat, by omega⟩
    exact pos j A x
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, p = 1 - j := ⟨(1 - p).toNat, by omega⟩
    exact neg j A x

end S_Rep_IsTateCupProduct_cup_mk_right_eq_tateMap
end P2MW
export P2MW.S_Rep_IsTateCupProduct_cup_mk_right_eq_tateMap (solution)

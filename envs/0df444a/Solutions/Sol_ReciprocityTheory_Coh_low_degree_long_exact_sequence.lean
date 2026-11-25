-- Prove2me | solution 1 for ReciprocityTheory.Coh.low_degree_long_exact_sequence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:42.89654+00:00
-- url     : https://prove2.me/submissions/a1687aeb-37a9-4435-96d1-6d4479086d41

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowNat
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowLES
import Theorems.Thm_ReciprocityTheory_Coh_lowLES_h0Equiv_pair
import Theorems.Thm_ReciprocityTheory_Coh_LowDeg_h1Equiv_pair
import Theorems.Thm_ReciprocityTheory_Coh_LowDeg_h2Equiv_pair
import Theorems.Thm_ReciprocityTheory_Coh_admissibility_holds
import Theorems.Thm_ReciprocityTheory_Coh_lES_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal LowDeg
universe u
section SlopeTestRemainingChoices
variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
end SlopeTestRemainingChoices
private theorem exact_of_linearEquiv_conj {R X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂] [AddCommGroup X₃] [Module R X₃]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂] [AddCommGroup Y₃] [Module R Y₃]
    {f : X₁ →ₗ[R] X₂} {g : X₂ →ₗ[R] X₃} {f' : Y₁ →ₗ[R] Y₂} {g' : Y₂ →ₗ[R] Y₃}
    (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂) (e₃ : X₃ ≃ₗ[R] Y₃)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (hg : ∀ x, e₃ (g x) = g' (e₂ x))
    (h : Function.Exact f g) : Function.Exact f' g' := by
  intro y
  obtain ⟨x, rfl⟩ := e₂.surjective y
  rw [← hg, LinearEquiv.map_eq_zero_iff, h x]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e₁ z, (hf z).symm⟩
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := e₁.surjective w
    refine ⟨z, e₂.injective ?_⟩
    rw [hf]
    exact hw
private theorem injective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Injective f) : Function.Injective f' := by
  intro a b hab
  obtain ⟨x, rfl⟩ := e₁.surjective a
  obtain ⟨z, rfl⟩ := e₁.surjective b
  rw [← hf, ← hf] at hab
  rw [h (e₂.injective hab)]
private theorem surjective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Surjective f) : Function.Surjective f' := by
  intro y
  obtain ⟨x, hx⟩ := h (e₂.symm y)
  refine ⟨e₁ x, ?_⟩
  rw [← hf, hx, LinearEquiv.apply_symm_apply]
end ReciprocityTheory.Coh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal LowDeg
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : LowLESStatement.{u} := by
  intro R _ G _ _ _ A B C i p hadm
  have hses := admissibility_holds R G A B C i p hadm
  obtain ⟨⟨δ, hconn, hles⟩, -⟩ := lES_holds R _ _ _ i.hom p.hom hses

  have n0 : ∀ x : C.H 0, h1EquivOfOrderTwo A (δ 0 x) =
      ((h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap) (cohomZeroEquivContinuous C x) := by
    intro x
    show h1EquivOfOrderTwo A (δ 0 x) = h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm (cohomZeroEquivContinuous C x)))
    rw [LinearEquiv.symm_apply_apply]
  have n1 : ∀ x : C.H 1, h2EquivOfOrderTwo A (δ 1 x) =
      ((h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap) (h1EquivOfOrderTwo C x) := by
    intro x
    show h2EquivOfOrderTwo A (δ 1 x) = h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (h1EquivOfOrderTwo C x)))
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨(h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap,
    (h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap, ?_, ?_,
    injective_of_linearEquiv_conj (cohomZeroEquivContinuous A) (cohomZeroEquivContinuous B) (fun x => lowLES_h0Equiv_pair i x) hles.inj,
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous A) (cohomZeroEquivContinuous B) (cohomZeroEquivContinuous C) (fun x => lowLES_h0Equiv_pair i x)
      (fun x => lowLES_h0Equiv_pair p x) (hles.exB 0),
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous B) (cohomZeroEquivContinuous C) (h1EquivOfOrderTwo A) (fun x => lowLES_h0Equiv_pair p x)
      n0 (hles.exC 0),
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous C) (h1EquivOfOrderTwo A) (h1EquivOfOrderTwo B) n0
      (fun x => h1Equiv_pair (P := i) (x := x)) (hles.exA 0),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo A) (h1EquivOfOrderTwo B) (h1EquivOfOrderTwo C) (fun x => h1Equiv_pair (P := i) (x := x))
      (fun x => h1Equiv_pair (P := p) (x := x)) (hles.exB 1),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo B) (h1EquivOfOrderTwo C) (h2EquivOfOrderTwo A) (fun x => h1Equiv_pair (P := p) (x := x))
      n1 (hles.exC 1),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo C) (h2EquivOfOrderTwo A) (h2EquivOfOrderTwo B) n1
      (fun x => h2Equiv_pair (P := i) (x := x)) (hles.exA 1),
    exact_of_linearEquiv_conj (h2EquivOfOrderTwo A) (h2EquivOfOrderTwo B) (h2EquivOfOrderTwo C) (fun x => h2Equiv_pair (P := i) (x := x))
      (fun x => h2Equiv_pair (P := p) (x := x)) (hles.exB 2),
    fun hsub => surjective_of_linearEquiv_conj (h2EquivOfOrderTwo B) (h2EquivOfOrderTwo C) (fun x => h2Equiv_pair (P := p) (x := x))
      (fun y => (hles.exC 2 y).1 (@Subsingleton.elim _ hsub _ _))⟩
  ·
    intro c b a hb ha
    let b₀ : B.coch.X 0 := ⟨fun _ => b, continuous_const⟩
    have hz : A.coch.d 1 ((oneCocyclesEquivFunctions A).symm a).1 = 0 := ((oneCocyclesEquivFunctions A).symm a).2
    have key : B.coch.d 0 b₀ = i.hom.f 1 ((oneCocyclesEquivFunctions A).symm a).1 := by
      apply Subtype.ext
      funext v
      show dn B.rho 0 (fun _ => b) v = i.u (a.1 (i.φ (v 0)))
      rw [hadm.i_id]
      show dn B.rho 0 (fun _ => b) v = i.u (a.1 (v 0))
      rw [ha (v 0), dn_zero_apply]
      all_goals rfl
    have hcd : C.coch.d 0 (p.hom.f 0 b₀) = 0 := by
      rw [← p.hom.comm, key]
      exact (hses.exact 1).apply_apply_eq_zero _
    have e₁ : (cohomZeroEquivContinuous C).symm c = C.coch.cls 0 (p.hom.f 0 b₀) hcd := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext hb.symm
    have e₂ : h1EquivOfOrderTwo A (A.coch.cls 1 _ hz) = Submodule.Quotient.mk a := by
      show Submodule.Quotient.mk (oneCocyclesEquivFunctions A ((oneCocyclesEquivFunctions A).symm a)) = _
      rw [LinearEquiv.apply_symm_apply]
    show h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm c)) = _
    rw [e₁, hconn 0 b₀ _ hcd hz key]
    exact e₂
  ·
    intro c b a hbc hpb hia
    let b₁ : B.coch.X 1 := ⟨fun v => b (v 0), hbc.comp (continuous_apply 0)⟩
    have hz : A.coch.d 2 ((twoCocyclesEquivFunctions A).symm a).1 = 0 := ((twoCocyclesEquivFunctions A).symm a).2
    have key : B.coch.d 1 b₁ = i.hom.f 2 ((twoCocyclesEquivFunctions A).symm a).1 := by
      apply Subtype.ext
      funext v
      show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (i.φ (v 0), i.φ (v 1)))
      rw [hadm.i_id]
      show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (v 0, v 1))
      rw [hia (v 0, v 1), dn_one_apply, d1_apply]
      all_goals rfl
    have hcd : C.coch.d 1 (p.hom.f 1 b₁) = 0 := by
      rw [← p.hom.comm, key]
      exact (hses.exact 2).apply_apply_eq_zero _
    have e₁ : (h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c) = C.coch.cls 1 (p.hom.f 1 b₁) hcd := by
      rw [LinearEquiv.symm_apply_eq]
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      show c.1 g = p.u (b (p.φ g))
      rw [hadm.p_id]
      exact (hpb g).symm
    have e₂ : h2EquivOfOrderTwo A (A.coch.cls 2 _ hz) = Submodule.Quotient.mk a := by
      show Submodule.Quotient.mk (twoCocyclesEquivFunctions A ((twoCocyclesEquivFunctions A).symm a)) = _
      rw [LinearEquiv.apply_symm_apply]
    show h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c))) = _
    rw [e₁, hconn 1 b₁ _ hcd hz key]
    exact e₂
end ReciprocityTheory.Coh

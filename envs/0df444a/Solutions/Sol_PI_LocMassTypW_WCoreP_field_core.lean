-- Prove2me | solution 1 for PI.LocMassTypW.WCoreP.field_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:33.774569+00:00
-- url     : https://prove2.me/submissions/057f5811-e364-46f7-acd6-d4dc68123d62

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings
import Theorems.Thm_PI_LocMassTypW_WCoreP_model_inj
import Theorems.Thm_PI_LocMassTypW_WCoreP_exists_Z

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypW PI.LocMassTypW.WCoreP
open Matrix Module
namespace PI.LocMassTypW.WCoreP
theorem _root_.solution {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (a0 a : W →ₗ[K] V) (b0 b : V →ₗ[K] W) (s0 s : W →ₗ[K] V)
    (ha0 : Function.Injective a0) (ha : Function.Injective a)
    (hs0 : ∀ w, b0 (s0 w) = w) (hs : ∀ w, b (s w) = w) (hc : ∀ w, b (a w) = b0 (a0 w)) :
    ∃ e : V ≃ₗ[K] V, (∀ w, e (a0 w) = a w) ∧ ∀ v, b (e v) = b0 v := by

  obtain ⟨T, hT⟩ := Submodule.exists_isCompl (LinearMap.range (b ∘ₗ a))
  obtain ⟨Z, hZb, hZa, hZd⟩ := exists_Z a b s ha hs
  obtain ⟨Z0, hZ0b, hZ0a, hZ0d⟩ := exists_Z a0 b0 s0 ha0 hs0
  have hba : b ∘ₗ a = b0 ∘ₗ a0 := LinearMap.ext hc
  have hTcond : ∀ w, b (a w) ∈ T → b (a w) = 0 := fun w h =>
    (Submodule.disjoint_def.mp hT.disjoint) _ ⟨w, rfl⟩ h
  have hT0cond : ∀ w, b0 (a0 w) ∈ T → b0 (a0 w) = 0 := fun w h => by
    rw [← hc] at h ⊢
    exact hTcond w h
  set F := LinearMap.coprod a (LinearMap.coprod (s ∘ₗ T.subtype) Z.subtype) with hF
  set F0 := LinearMap.coprod a0 (LinearMap.coprod (s0 ∘ₗ T.subtype) Z0.subtype) with hF0
  have hFi : Function.Injective F :=
    model_inj a b s T Z.subtype ha hs hTcond Subtype.val_injective
      (fun z => LinearMap.mem_ker.mp (hZb z.2)) (fun z w h => hZa z z.2 ⟨w, h.symm⟩)
  have hF0i : Function.Injective F0 :=
    model_inj a0 b0 s0 T Z0.subtype ha0 hs0 hT0cond Subtype.val_injective
      (fun z => LinearMap.mem_ker.mp (hZ0b z.2)) (fun z w h => hZ0a z z.2 ⟨w, h.symm⟩)
  have hTd : finrank K T = finrank K (LinearMap.ker (b ∘ₗ a)) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hT
    have h2 := LinearMap.finrank_range_add_finrank_ker (b ∘ₗ a)
    omega
  have hdim : finrank K (W × T × Z) = finrank K V := by
    rw [Module.finrank_prod, Module.finrank_prod, hTd]
    omega
  have hdim0 : finrank K (W × T × Z0) = finrank K V := by
    rw [Module.finrank_prod, Module.finrank_prod, hTd, hba]
    omega
  have hZZ : finrank K Z0 = finrank K Z := by
    have h1 := hZd
    have h2 := hZ0d
    rw [hba] at h1
    omega
  let EF : (W × T × Z) ≃ₗ[K] V := LinearEquiv.ofBijective F
    ⟨hFi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hFi⟩
  let EF0 : (W × T × Z0) ≃ₗ[K] V := LinearEquiv.ofBijective F0
    ⟨hF0i, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim0).mp hF0i⟩
  let φ : Z0 ≃ₗ[K] Z := LinearEquiv.ofFinrankEq Z0 Z hZZ
  let G : (W × T × Z0) ≃ₗ[K] (W × T × Z) :=
    (LinearEquiv.refl K W).prodCongr ((LinearEquiv.refl K T).prodCongr φ)
  refine ⟨EF0.symm.trans (G.trans EF), fun w => ?_, fun v => ?_⟩
  · have h1 : EF0.symm (a0 w) = (w, 0, 0) := by
      rw [LinearEquiv.symm_apply_eq]
      show a0 w = F0 (w, 0, 0)
      simp [hF0]
    simp only [LinearEquiv.trans_apply, h1]
    show F (G (w, 0, 0)) = a w
    simp [hF, G]
  · obtain ⟨⟨w, t, z0⟩, rfl⟩ := EF0.surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    show b (F (G (w, t, z0))) = b0 (F0 (w, t, z0))
    have hz : b (φ z0 : V) = 0 := LinearMap.mem_ker.mp (hZb (φ z0).2)
    have hz0 : b0 (z0 : V) = 0 := LinearMap.mem_ker.mp (hZ0b z0.2)
    simp only [hF, hF0, G, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, LinearMap.coprod_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, map_add, hs, hs0, hz, hz0, hc]
end PI.LocMassTypW.WCoreP

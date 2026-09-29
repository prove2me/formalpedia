-- Prove2me | solution 1 for TensorProduct.exists_linearEquiv_compHom_ringEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/dead01c6-b7fa-5da7-a8be-91e17dd23bcb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TensorProduct_exists_linearEquiv_compHom_ringEquiv_tmul

set_option autoImplicit false

open scoped TensorProduct

namespace TensorAlongRingEquiv

theorem finite_iff_and_finrank_eq {k κ : Type} [Field k] [Field κ] (e : k ≃+* κ)
    (H : Type) [AddCommGroup H] [Module κ H] :
    letI : Module k H := Module.compHom H e.toRingHom
    (Module.Finite k H ↔ Module.Finite κ H) ∧ Module.finrank k H = Module.finrank κ H := by
  letI ik : Module k H := Module.compHom H e.toRingHom

  have hke : ∀ (c : k) (x : H), (e c) • x = c • x := fun c x => rfl
  have hek : ∀ (c : κ) (x : H), (e.symm c) • x = c • x := by
    intro c x; show e (e.symm c) • x = c • x; rw [e.apply_symm_apply]
  have h1 : Module.Finite k H ↔ Module.Finite κ H := by
    constructor
    · intro hk
      haveI := hk
      exact Module.Finite.of_basis ((Module.finBasis k H).mapCoeffs e hke)
    · intro hκ
      haveI := hκ
      exact Module.Finite.of_basis ((Module.finBasis κ H).mapCoeffs e.symm hek)
  refine ⟨h1, ?_⟩
  by_cases hκ : Module.Finite κ H
  · haveI := hκ
    rw [Module.finrank_eq_card_basis ((Module.finBasis κ H).mapCoeffs e.symm hek), Fintype.card_fin]
  · rw [Module.finrank_of_not_finite hκ, Module.finrank_of_not_finite (fun h => hκ (h1.1 h))]

end TensorAlongRingEquiv

theorem solution
    {k κ : Type} [Field k] [Field κ] (e : k ≃+* κ)
    (V : Type) [AddCommGroup V] [Module k V] (H : Type) [AddCommGroup H] [Module κ H] :
    letI : Module κ V := Module.compHom V (e.symm : κ ≃+* k).toRingHom
    letI : Module k H := Module.compHom H e.toRingHom
    letI : Module k (V ⊗[κ] H) := Module.compHom (V ⊗[κ] H) e.toRingHom
    (Module.Finite k H ↔ Module.Finite κ H) ∧
    Module.finrank k H = Module.finrank κ H ∧
    ∃ Θ : (V ⊗[k] H) ≃ₗ[k] (V ⊗[κ] H),
      (∀ (v : V) (h : H), Θ (v ⊗ₜ[k] h) = v ⊗ₜ[κ] h) ∧
      (∀ (f : V →ₗ[k] V) (f' : V →ₗ[κ] V) (_ : ∀ v, f' v = f v) (g : H →ₗ[κ] H) (g' : H →ₗ[k] H) (_ : ∀ h, g' h = g h)
          (x : V ⊗[k] H),
        Θ (TensorProduct.map f g' x) = TensorProduct.map f' g (Θ x)) := by
  letI iκV : Module κ V := Module.compHom V (e.symm : κ ≃+* k).toRingHom
  letI ikH : Module k H := Module.compHom H e.toRingHom
  letI ikT : Module k (V ⊗[κ] H) := Module.compHom (V ⊗[κ] H) e.toRingHom
  obtain ⟨h1, h2⟩ := TensorAlongRingEquiv.finite_iff_and_finrank_eq e H
  refine ⟨h1, h2, ?_⟩

  have sV : ∀ (c : κ) (v : V), c • v = (e.symm c) • v := fun _ _ => rfl
  have sH : ∀ (a : k) (h : H), a • h = (e a) • h := fun _ _ => rfl
  have sT : ∀ (a : k) (t : V ⊗[κ] H), a • t = (e a) • t := fun _ _ => rfl

  let φ : V →ₗ[k] H →ₗ[k] (V ⊗[κ] H) :=
    LinearMap.mk₂ k (fun (v : V) (h : H) => v ⊗ₜ[κ] h)
      (fun v₁ v₂ h => TensorProduct.add_tmul v₁ v₂ h)
      (fun a v h => by
        rw [sT, TensorProduct.smul_tmul', sV, e.symm_apply_apply])
      (fun v h₁ h₂ => TensorProduct.tmul_add v h₁ h₂)
      (fun a v h => by
        rw [sH, TensorProduct.tmul_smul, sT])
  let Θ₀ : V ⊗[k] H →ₗ[k] V ⊗[κ] H := TensorProduct.lift φ
  have hΘ₀ : ∀ (v : V) (h : H), Θ₀ (v ⊗ₜ[k] h) = v ⊗ₜ[κ] h := fun v h => TensorProduct.lift.tmul v h

  letI iκT : Module κ (V ⊗[k] H) := Module.compHom (V ⊗[k] H) (e.symm : κ ≃+* k).toRingHom
  have sT' : ∀ (c : κ) (t : V ⊗[k] H), c • t = (e.symm c) • t := fun _ _ => rfl
  let ψ : V →ₗ[κ] H →ₗ[κ] (V ⊗[k] H) :=
    LinearMap.mk₂ κ (fun (v : V) (h : H) => v ⊗ₜ[k] h)
      (fun v₁ v₂ h => TensorProduct.add_tmul v₁ v₂ h)
      (fun c v h => by
        rw [sT', TensorProduct.smul_tmul']
        rfl)
      (fun v h₁ h₂ => TensorProduct.tmul_add v h₁ h₂)
      (fun c v h => by
        rw [sT', TensorProduct.smul_tmul', TensorProduct.smul_tmul, sH, e.apply_symm_apply])
  let Ω₀ : V ⊗[κ] H →ₗ[κ] V ⊗[k] H := TensorProduct.lift ψ
  have hΩ₀ : ∀ (v : V) (h : H), Ω₀ (v ⊗ₜ[κ] h) = v ⊗ₜ[k] h := fun v h => TensorProduct.lift.tmul v h

  let Ω : V ⊗[κ] H →ₗ[k] V ⊗[k] H :=
    { toFun := Ω₀
      map_add' := fun x y => Ω₀.map_add x y
      map_smul' := fun a t => by
        show Ω₀ (a • t) = a • Ω₀ t
        rw [sT, Ω₀.map_smul, sT', e.symm_apply_apply] }
  have hΩ : ∀ t, Ω t = Ω₀ t := fun _ => rfl
  have left : ∀ x : V ⊗[k] H, Ω (Θ₀ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul v h => rw [hΘ₀, hΩ, hΩ₀]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have right : ∀ y : V ⊗[κ] H, Θ₀ (Ω y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul v h => rw [hΩ, hΩ₀, hΘ₀]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let Θ : (V ⊗[k] H) ≃ₗ[k] (V ⊗[κ] H) :=
    { toLinearMap := Θ₀
      invFun := Ω
      left_inv := left
      right_inv := right }
  have hΘ : ∀ x, Θ x = Θ₀ x := fun _ => rfl
  refine ⟨Θ, fun v h => by rw [hΘ, hΘ₀], ?_⟩
  intro f f' hf g g' hg x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v h => rw [TensorProduct.map_tmul, hΘ, hΘ₀, hΘ, hΘ₀, TensorProduct.map_tmul, hf, hg]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end S_TensorProduct_exists_linearEquiv_compHom_ringEquiv_tmul
end P2MW
export P2MW.S_TensorProduct_exists_linearEquiv_compHom_ringEquiv_tmul (solution)

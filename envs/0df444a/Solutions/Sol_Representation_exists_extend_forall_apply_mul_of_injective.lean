-- Prove2me | solution 1 for Representation.exists_extend_forall_apply_mul_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9b4dd0f9-fa3c-5972-988a-a6f91d7bbb1c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_extend_forall_apply_mul_of_injective

set_option autoImplicit false

universe u v w

open scoped Classical in
theorem solution
    {H : Type u} {G : Type v} [Group H] [Group G] {W : Type w} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ k : H, ∀ v ∈ P, ρ k v ∈ P)
    (T : P →ₗ[ℂ] (G → ℂ))
    (hT : ∀ (k : H) (v : P) (x : G), T ⟨ρ k v, hP k v v.2⟩ x = T v (x * ι k)) :
    ∃ T' : W →ₗ[ℂ] (G → ℂ),
      (∀ (k : H) (v : W) (x : G), T' (ρ k v) x = T' v (x * ι k)) ∧ ∀ v : P, T' v = T v := by
  classical
  set S : Subgroup G := ι.range with hS

  let sec : G → G := fun x => (QuotientGroup.mk x : G ⧸ S).out
  have hx : ∀ x : G, ∃ k : H, x = sec x * ι k := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S x
    obtain ⟨k, hk⟩ := h.2
    refine ⟨k⁻¹, ?_⟩
    show x = (QuotientGroup.mk x : G ⧸ S).out * ι k⁻¹
    rw [hh, map_inv, hk, mul_inv_cancel_right]
  let kof : G → H := fun x => (hx x).choose
  have hkof : ∀ x, x = sec x * ι (kof x) := fun x => (hx x).choose_spec
  have hsec : ∀ (x : G) (k : H), sec (x * ι k) = sec x := by
    intro x k
    show (QuotientGroup.mk (x * ι k) : G ⧸ S).out = (QuotientGroup.mk x : G ⧸ S).out
    congr 1
    apply QuotientGroup.eq.mpr
    refine ⟨k⁻¹, ?_⟩
    rw [map_inv]; group
  have hkof_mul : ∀ (x : G) (k : H), kof (x * ι k) = kof x * k := by
    intro x k
    apply hι
    have h1 := hkof (x * ι k)
    rw [hsec] at h1
    have h2 := hkof x

    rw [map_mul]
    apply mul_left_cancel (a := sec x)
    rw [← mul_assoc, ← h2]; exact h1.symm

  obtain ⟨Pc, hPc⟩ := Submodule.exists_isCompl P
  let π : W →ₗ[ℂ] P := Submodule.linearProjOfIsCompl P Pc hPc
  have hπ : ∀ v : P, π v = v := fun v => Submodule.linearProjOfIsCompl_apply_left hPc v
  let ℓ : G → W →ₗ[ℂ] ℂ := fun r => (LinearMap.proj r).comp (T.comp π)
  have hℓ : ∀ (r : G) (v : P), ℓ r v = T v r := fun r v => by
    simp only [ℓ, LinearMap.comp_apply, LinearMap.proj_apply, hπ]

  let T' : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun v x => ℓ (sec x) (ρ (kof x) v)
      map_add' := fun v w => by funext x; simp only [map_add, Pi.add_apply]
      map_smul' := fun c v => by funext x; simp only [map_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨T', ?_, ?_⟩
  · intro k v x
    show ℓ (sec x) (ρ (kof x) (ρ k v)) = ℓ (sec (x * ι k)) (ρ (kof (x * ι k)) v)
    rw [hsec, hkof_mul, map_mul]; rfl
  · intro v
    funext x
    show ℓ (sec x) (ρ (kof x) v) = T v x
    have hmem : ρ (kof x) v ∈ P := hP _ _ v.2
    have : ℓ (sec x) (ρ (kof x) (v : W)) = ℓ (sec x) ((⟨ρ (kof x) v, hmem⟩ : P) : W) := rfl
    rw [this, hℓ, hT, ← hkof]

end S_Representation_exists_extend_forall_apply_mul_of_injective
end P2MW
export P2MW.S_Representation_exists_extend_forall_apply_mul_of_injective (solution)

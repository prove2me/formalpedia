-- Prove2me | solution 1 for QLLL.LinearMap.exists_comp_add_comp
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:48:09.255014+00:00
-- url     : https://prove2.me/submissions/f281cb91-3a51-45fe-830f-77f748e2c4d4

import Mathlib

section

open TensorProduct LinearMap Function
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
open _root_.LinearMap
variable {M N H : Type*}
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup H] [Module K H]

theorem solution (f : V →ₗ[K] M) (g : V →ₗ[K] N) (h : V →ₗ[K] H)
    (hker : ker f ⊓ ker g ≤ ker h) :
    ∃ (u : M →ₗ[K] H) (v : N →ₗ[K] H), h = u ∘ₗ f + v ∘ₗ g := by
  set p : V →ₗ[K] M × N := f.prod g with hp
  have hkerp : ker p ≤ ker h := by rw [hp, LinearMap.ker_prod]; exact hker
  let hbar : (V ⧸ ker p) →ₗ[K] H := (ker p).liftQ h hkerp
  let hr : (range p) →ₗ[K] H := hbar ∘ₗ (p.quotKerEquivRange.symm : _ →ₗ[K] _)
  obtain ⟨Φ, hΦ⟩ := hr.exists_extend
  have key : ∀ x : V, Φ (p x) = h x := by
    intro x
    have hmem : p x ∈ range p := ⟨x, rfl⟩
    have h1 := congrArg (fun F : (range p) →ₗ[K] H => F ⟨p x, hmem⟩) hΦ
    have h2 : p.quotKerEquivRange (Submodule.Quotient.mk x) = ⟨p x, hmem⟩ := rfl
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    simp only [hr, LinearMap.comp_apply, ← h2, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, hbar, Submodule.liftQ_apply]
  refine ⟨Φ ∘ₗ LinearMap.inl K M N, Φ ∘ₗ LinearMap.inr K M N, ?_⟩
  ext x
  have hsplit : (f x, g x) = (f x, (0 : N)) + ((0 : M), g x) := by simp
  have : Φ (p x) = Φ (f x, 0) + Φ (0, g x) := by
    rw [show p x = (f x, g x) from rfl, hsplit, map_add]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.inr_apply]
  rw [← key x, this]

end

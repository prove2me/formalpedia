-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P18.crossedModule_strictTwoGroup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:07:50.845374+00:00
-- url     : https://prove2.me/submissions/fcedf5ed-90b0-476a-9b71-df3b2e4ce4c3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P18
open QAlgorithms.Papers.Independent.Renew46.P18

universe u v w x

theorem solution
    {H : Type u} {G : Type v} [Group H] [Group G]
    (tau : H →* G) (rho : G →* MulAut H) (h : IsCrossedModule tau rho) :
    IsStrictTwoGroup (crossedSource rho) (crossedTarget tau rho)
      (crossedIdentity rho) (crossedCompose rho) (crossedArrowInverse tau rho) := by
  obtain ⟨h1, h2⟩ := h
  have hr : ∀ (k : H) (g : G) (x : H), rho (tau k * g) x = k * rho g x * k⁻¹ := by
    intro k g x
    rw [map_mul, MulAut.mul_apply, h2]
  unfold IsStrictTwoGroup crossedSource crossedTarget crossedIdentity crossedCompose
    crossedArrowInverse
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; simp
  · intro a b hb; refine ⟨rfl, ?_⟩; simp only [map_mul, hb]; group
  · intro a; constructor <;> ext <;> simp
  · intro a b c _ _; ext <;> simp [mul_assoc]
  · intro a
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp
    · ext <;> simp
    · ext <;> simp
  · rfl
  · simp
  · rfl
  · intro a b
    refine ⟨rfl, ?_⟩
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul, h1]
    group
  · intro a b; ext <;> simp
  · intro a b c d hab hcd
    ext
    · simp only [SemidirectProduct.mul_left, hab, hr]
      simp only [map_mul]
      group
    · simp
  · intro a
    refine ⟨rfl, ?_⟩
    simp only [SemidirectProduct.inv_left, SemidirectProduct.inv_right]
    rw [h1, map_inv]
    group
  · intro a; ext <;> simp
  · intro a b hab
    ext
    · simp only [SemidirectProduct.inv_left, hab]
      rw [mul_inv_rev, ← map_inv tau, map_mul, MulAut.mul_apply, h2]
      simp only [map_mul, map_inv]
      group
    · simp

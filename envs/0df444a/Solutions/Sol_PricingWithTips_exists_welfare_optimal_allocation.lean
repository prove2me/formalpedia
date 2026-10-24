-- Prove2me | solution 1 for PricingWithTips.exists_welfare_optimal_allocation
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:23:35.099303+00:00
-- url     : https://prove2.me/submissions/919027fb-0c2e-478e-9879-5303c3918d88

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution (M : Market B S D) :
    ∃ A : Allocation B S D, IsWelfareOptimal M A := by
  classical
  let A₀ : Allocation B S D := {
    assigned := fun _ => none
    store_unique := by
      intro b₁ b₂ s d₁ d₂ h₁ h₂
      simp at h₁
    courier_unique := by
      intro b₁ b₂ s₁ s₂ d h₁ h₂
      simp at h₁
  }
  haveI : Nonempty (Allocation B S D) := ⟨A₀⟩
  haveI : Finite (Allocation B S D) :=
    Finite.of_injective Allocation.assigned (by
      intro A A' h
      cases A
      cases A'
      cases h
      rfl)
  obtain ⟨A, hA⟩ := Finite.exists_max (welfare M)
  exact ⟨A, hA⟩

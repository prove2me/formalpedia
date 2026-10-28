-- Prove2me | solution 1 for SetOptLattice.Existence.remark_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:00:07.633863+00:00
-- url     : https://prove2.me/submissions/fc69d7bf-554e-4f69-9a09-d6a711225a84

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

open SetOptLattice.Existence
namespace Aux_SetOptLattice_R33
open SetOptLattice.Existence

theorem epsBound_mono (a : EReal) {ε₁ ε₂ : ℝ} (h0 : 0 ≤ ε₁) (h12 : ε₁ ≤ ε₂) :
    epsBound a ε₁ ≤ epsBound a ε₂ := by
  unfold epsBound
  by_cases ha : a = ⊥
  · rw [if_pos ha, if_pos ha]
    by_cases he : ε₁ = 0
    · rw [if_pos he]; exact bot_le
    · have h1 : 0 < ε₁ := lt_of_le_of_ne h0 (Ne.symm he)
      have h2 : 0 < ε₂ := lt_of_lt_of_le h1 h12
      rw [if_neg he, if_neg (ne_of_gt h2)]
      apply EReal.coe_le_coe_iff.mpr
      have : 1 / ε₂ ≤ 1 / ε₁ := one_div_le_one_div_of_le h1 h12
      have e1 : -1 / ε₁ = -(1 / ε₁) := by ring
      have e2 : -1 / ε₂ = -(1 / ε₂) := by ring
      rw [e1, e2]
      linarith
  · rw [if_neg ha, if_neg ha]
    exact add_le_add_right (EReal.coe_le_coe_iff.mpr h12) a

end Aux_SetOptLattice_R33

open Set Filter Topology
open scoped Pointwise


theorem solution {X Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x)) :
    (∀ ε₁ ε₂ : ℝ, 0 ≤ ε₁ → ε₁ ≤ ε₂ →
        MinSet Ψ f ε₁ ⊆ MinSet Ψ f ε₂ ∧ MinPlusSet Ψ f ε₁ ⊆ MinPlusSet Ψ f ε₂) ∧
      (∀ ε : ℝ, 0 ≤ ε → MinSet Ψ f ε ⊆ MinPlusSet Ψ f ε) ∧
      (∀ ε : ℝ, 0 ≤ ε → MinPlusSet Ψ f ε = ⋂ (δ : ℝ) (_ : 0 < δ), MinSet Ψ f (ε + δ)) ∧
      MinPlusSet Ψ f 0 = ⋂ (ε : ℝ) (_ : 0 < ε), MinSet Ψ f ε ∧
      MinPlusSet Ψ f 0 = ⋂ (ε : ℝ) (_ : 0 < ε), MinPlusSet Ψ f ε := by
  open Aux_SetOptLattice_R33 in
  refine ⟨fun ε₁ ε₂ h0 h12 => ⟨?_, ?_⟩, fun ε h0 => ?_, fun ε h0 => ?_, ?_, ?_⟩
  · rintro x ⟨ψ, hψ, h⟩
    exact ⟨ψ, hψ, le_trans h (epsBound_mono _ h0 h12)⟩
  · intro x hx δ hδ
    obtain ⟨ψ, hψ, h⟩ := hx δ hδ
    exact ⟨ψ, hψ, le_trans h (epsBound_mono _ (by linarith) (by linarith))⟩
  · rintro x ⟨ψ, hψ, h⟩ δ hδ
    exact ⟨ψ, hψ, le_trans h (epsBound_mono _ h0 (by linarith))⟩
  · ext x
    simp only [MinPlusSet, MinSet, mem_iInter, mem_setOf_eq]
  · ext x
    simp only [MinPlusSet, MinSet, mem_iInter, mem_setOf_eq, zero_add]
  · ext x
    simp only [mem_iInter]
    constructor
    · intro hx ε hε δ hδ
      obtain ⟨ψ, hψ, h⟩ := hx (ε + δ) (by linarith)
      exact ⟨ψ, hψ, by rw [zero_add] at h; exact h⟩
    · intro hx δ hδ
      obtain ⟨ψ, hψ, h⟩ := hx (δ / 2) (by linarith) (δ / 2) (by linarith)
      exact ⟨ψ, hψ, by rw [zero_add]; rw [add_halves] at h; exact h⟩

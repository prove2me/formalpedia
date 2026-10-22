-- Prove2me | solution 1 for SymBoolPCSP.LPRounding.completeness
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:37:06.750826+00:00
-- url     : https://prove2.me/submissions/64a171d7-a6f2-43fb-b937-8e859c24921b

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_LPRounding_Basic
set_option autoImplicit false
open PCSPBLPAff.Symmetric
open SymBoolPCSP.LPRounding

theorem solution {τ : Type} {ar : τ → ℕ} (𝔸 : RelStruct τ ar Bool) (X : Instance τ ar)
    (hsat : SatIn X 𝔸) : LPAlgAccepts 𝔸 X := by
  classical
  obtain ⟨σ, hσ⟩ := hsat
  have hsol : IsHullLPSol 𝔸 X (fun i => if σ i then (1 : ℚ) else 0) := by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · by_cases h : σ i <;> simp [h]
    · refine ⟨fun y => if y = σ ∘ X.scope j then 1 else 0, ?_, ?_, ?_, ?_⟩
      · intro y; by_cases h : y = σ ∘ X.scope j <;> simp [h]
      · intro y hy
        have : y ≠ σ ∘ X.scope j := fun h => hy (h ▸ hσ j)
        simp [this]
      · simp
      · intro c
        rw [Finset.sum_eq_single (σ ∘ X.scope j)]
        · simp [Function.comp]
        · intro y _ hy; simp [hy]
        · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨⟨_, hsol⟩, fun j => ?_⟩
  by_cases h : σ j
  · exact Or.inr ⟨_, hsol, by simp [h]⟩
  · exact Or.inl ⟨_, hsol, by simp [h]⟩

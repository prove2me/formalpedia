-- Prove2me | solution 1 for ShortBroadcastDom.proposition_5_1_rounding_with_slack
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T10:02:53.376073+00:00
-- url     : https://prove2.me/submissions/7463f44a-ec7b-4574-bc36-24e908368f48

import Mathlib
import Definitions.Def_ShortBroadcastDom_HasSlack

open ShortBroadcastDom in
theorem solution {X : Type} (Cx : X → ℝ) (Dx : X → ℕ) :
    (∀ δ τ : ℝ, HasSlack Cx Dx δ → ∀ x, Cx x ≤ (1 + δ) * τ → (Dx x : ℝ) ≤ τ) ∧
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (S : ι → X → ℝ) (α β : ι → ℝ),
      (∀ i x, 0 ≤ S i x) → (∀ i, 0 < α i) → (∀ i, 0 < β i) →
      (∀ x, ∑ i, α i * S i x ≤ Cx x - Dx x) → (∀ x, (Dx x : ℝ) ≤ ∑ i, β i * S i x) →
        HasSlack Cx Dx (Finset.univ.inf' Finset.univ_nonempty fun i => α i / β i) := by
  constructor
  · intro δ τ ⟨hδ, hC⟩ x hx
    have h1 := hC x
    have h2 : (1 + δ) * (Dx x : ℝ) ≤ (1 + δ) * τ := h1.trans hx
    exact le_of_mul_le_mul_left h2 (by linarith)
  · intro ι _ _ S α β hS hα hβ hCD hD
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = Finset.univ.inf' Finset.univ_nonempty fun i => α i / β i :=
      ⟨_, rfl⟩
    rw [← hδ]
    have hle : ∀ i, δ ≤ α i / β i := by
      intro i
      rw [hδ]
      exact Finset.inf'_le (fun i => α i / β i) (Finset.mem_univ i)
    have hpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]
      intro i _
      exact div_pos (hα i) (hβ i)
    refine ⟨hpos, fun x => ?_⟩
    have hsum : δ * ∑ i, β i * S i x ≤ ∑ i, α i * S i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have h1 : δ * β i ≤ α i := by
        have := hle i
        rwa [le_div_iff₀ (hβ i)] at this
      have := hS i x
      nlinarith
    have h1 := hCD x
    have h2 := hD x
    have h3 : δ * (Dx x : ℝ) ≤ δ * ∑ i, β i * S i x := mul_le_mul_of_nonneg_left h2 hpos.le
    nlinarith

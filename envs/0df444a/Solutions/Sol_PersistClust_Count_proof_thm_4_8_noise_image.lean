-- Prove2me | solution 1 for PersistClust.Count.proof_thm_4_8_noise_image
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T07:43:30.284972+00:00
-- url     : https://prove2.me/submissions/4463b695-ef42-43f1-80b9-d6fe5b34a64b

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

open PersistClust.Count
open scoped ENNReal

theorem solution
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂) :
    ∀ (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D q.1), q.1 ∈ DeltaN d₁ →
      pt (γ (Sum.inl ⟨q, hq⟩)) ∈ DeltaN (d₁ + 2 * c * δ) ∪ LamW (d₁ + 2 * c * δ) := by
  intro q hq hqin
  obtain ⟨hi, hii, hiii, hiv⟩ := hγ
  set a : Copies D := Sum.inl ⟨q, hq⟩ with ha
  have hpt_a : pt a = q.1 := by rw [ha]; rfl
  have hcδ : 0 < c * δ := mul_pos hc hδ
  have hznn : (0 : ℕ∞) ≤ (q.2 : ℕ∞) := (zero_le : (0 : ℕ∞) ≤ (q.2 : ℕ∞))
  -- basic facts about the point q
  have hDq : D q.1 ≠ 0 := ne_of_gt (lt_of_le_of_lt hznn hq)
  have hxy : q.1.2 < q.1.1 := hD q.1 hDq
  have hqin' : q.1.1 - (d₁ : EReal) < q.1.2 := hqin
  have hy_ne_top : q.1.2 ≠ ⊤ := by
    intro h; rw [h] at hxy; exact not_lt_of_ge le_top hxy
  have hx_ne_bot : q.1.1 ≠ ⊥ := by
    intro h; rw [h] at hxy; exact not_lt_of_ge bot_le hxy
  have hx_ne_top : q.1.1 ≠ ⊤ := by
    intro h
    have : (⊤ : EReal) < q.1.2 := by
      rw [h] at hqin'
      rwa [EReal.top_sub_coe] at hqin'
    exact not_lt_of_ge le_top this
  have hy_ne_bot : q.1.2 ≠ ⊥ := by
    intro h
    rw [h] at hqin'
    exact not_lt_of_ge bot_le hqin'
  have hxr : ((q.1.1).toReal : EReal) = q.1.1 := EReal.coe_toReal hx_ne_top hx_ne_bot
  have hyr : ((q.1.2).toReal : EReal) = q.1.2 := EReal.coe_toReal hy_ne_top hy_ne_bot
  have hqin_real : (q.1.1).toReal - d₁ < (q.1.2).toReal := by
    have h1 := hqin'
    rw [← hxr, ← hyr] at h1
    rw [← EReal.coe_sub] at h1
    exact EReal.coe_lt_coe_iff.mp h1
  -- the image's x-coordinate is either ≤ cδ, or bounded by the source's x-coordinate
  have hbound : ∀ a : Copies D,
      (pt (γ a)).1 ≤ (pt a).1 + ((c * δ : ℝ) : EReal) ∨ (pt (γ a)).1 ≤ ((c * δ : ℝ) : EReal) := by
    intro a
    by_cases h : (pt (γ a)).1 ≤ ((c * δ : ℝ) : EReal)
    · exact Or.inr h
    · left
      have hlt : ((c * δ : ℝ) : EReal) < (pt (γ a)).1 := not_le.mp h
      by_cases hy : (pt (γ a)).2 ≤ ((c * δ : ℝ) : EReal)
      · have hmem : pt (γ a) ∈ QSE (c * δ) := ⟨hlt, hy⟩
        have hh := hiv (γ a) hmem
        rw [Equiv.symm_apply_apply] at hh
        exact hh.2
      · have hy' : ((c * δ : ℝ) : EReal) < (pt (γ a)).2 := not_le.mp hy
        have hmem : pt (γ a) ∈ QNE (c * δ) := ⟨hlt, hy'⟩
        have hh := (hii (γ a) hmem).1
        rw [Equiv.symm_apply_apply] at hh
        exact hh.2
  by_cases hcase : q.1.2 ≤ ((c * δ : ℝ) : EReal)
  · -- Case A: `y ≤ cδ`; the image lies in `Λ^W`.
    right
    change (pt (γ a)).1 ≤ ((d₁ + 2 * c * δ : ℝ) : EReal)
    have hyr_le : (q.1.2).toReal ≤ c * δ := by
      have h1 : ((q.1.2).toReal : EReal) ≤ ((c * δ : ℝ) : EReal) := by rw [hyr]; exact hcase
      exact EReal.coe_le_coe_iff.mp h1
    have hx_lt : (q.1.1).toReal < d₁ + c * δ := by linarith
    have hC := hbound a
    rcases hC with hC | hC
    · have hlt : (pt a).1 + ((c * δ : ℝ) : EReal) <
          ((d₁ + 2 * c * δ : ℝ) : EReal) := by
        rw [hpt_a, ← hxr, ← EReal.coe_add]
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
      exact le_of_lt (lt_of_le_of_lt hC hlt)
    · refine le_trans hC ?_
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  · -- Case B: `cδ < y`; the image lies in `Δ^N`.
    left
    change (pt (γ a)).1 - ((d₁ + 2 * c * δ : ℝ) : EReal) < (pt (γ a)).2
    have hcase' : ((c * δ : ℝ) : EReal) < q.1.2 := not_le.mp hcase
    have hmem : pt a ∈ QNE (c * δ) := by
      rw [hpt_a]
      exact ⟨lt_of_lt_of_le hcase' (le_of_lt hxy), hcase'⟩
    have hclose := hi a hmem
    rw [hpt_a] at hclose
    have hx' : (pt (γ a)).1 ≤ q.1.1 + ((c * δ : ℝ) : EReal) := hclose.1.2
    have hy' : q.1.2 - ((c * δ : ℝ) : EReal) ≤ (pt (γ a)).2 :=
      EReal.sub_le_of_le_add hclose.2.1
    have hx'_ne_bot : (pt (γ a)).1 ≠ ⊥ := by
      intro h
      have hle : q.1.1 - ((c * δ : ℝ) : EReal) ≤ (pt (γ a)).1 :=
        EReal.sub_le_of_le_add hclose.1.1
      rw [h] at hle
      have hne : q.1.1 - ((c * δ : ℝ) : EReal) ≠ ⊥ := by
        rw [← hxr, ← EReal.coe_sub]; exact EReal.coe_ne_bot _
      exact hne (le_antisymm hle bot_le)
    have hx'_ne_top : (pt (γ a)).1 ≠ ⊤ := by
      intro h
      have hlt : q.1.1 + ((c * δ : ℝ) : EReal) < (⊤ : EReal) := by
        rw [← hxr, ← EReal.coe_add]; exact EReal.coe_lt_top _
      rw [h] at hx'
      exact not_lt_of_ge hx' hlt
    have hy'_ne_bot : (pt (γ a)).2 ≠ ⊥ := by
      intro h
      have hle : q.1.2 - ((c * δ : ℝ) : EReal) ≤ (pt (γ a)).2 := hy'
      rw [h] at hle
      have hne : q.1.2 - ((c * δ : ℝ) : EReal) ≠ ⊥ := by
        rw [← hyr, ← EReal.coe_sub]; exact EReal.coe_ne_bot _
      exact hne (le_antisymm hle bot_le)
    have hy'_ne_top : (pt (γ a)).2 ≠ ⊤ := by
      intro h
      have hlt : q.1.2 + ((c * δ : ℝ) : EReal) < (⊤ : EReal) := by
        rw [← hyr, ← EReal.coe_add]; exact EReal.coe_lt_top _
      have h2 : (pt (γ a)).2 ≤ q.1.2 + ((c * δ : ℝ) : EReal) := hclose.2.2
      rw [h] at h2
      exact not_lt_of_ge h2 hlt
    have goal_real :
        (pt (γ a)).1.toReal - (d₁ + 2 * c * δ) < (pt (γ a)).2.toReal := by
      have hx'le : (pt (γ a)).1.toReal ≤ (q.1.1).toReal + c * δ := by
        have h1 := hx'
        rw [← EReal.coe_toReal hx'_ne_top hx'_ne_bot, ← hxr, ← EReal.coe_add] at h1
        exact EReal.coe_le_coe_iff.mp h1
      have hy'ge : (q.1.2).toReal - c * δ ≤ (pt (γ a)).2.toReal := by
        have h1 := hy'
        rw [← EReal.coe_toReal hy'_ne_top hy'_ne_bot, ← hyr, ← EReal.coe_sub] at h1
        exact EReal.coe_le_coe_iff.mp h1
      have hxlt : (q.1.1).toReal - d₁ < (q.1.2).toReal := hqin_real
      linarith
    rw [← EReal.coe_toReal hx'_ne_top hx'_ne_bot,
        ← EReal.coe_toReal hy'_ne_top hy'_ne_bot,
        ← EReal.coe_sub]
    exact EReal.coe_lt_coe_iff.mpr goal_real

-- Prove2me | solution 1 for SLemma.concave_convex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:16:49.573915+00:00
-- url     : https://prove2.me/submissions/3eb654e5-cb79-4fb1-bc6b-c40af638cb20

import Mathlib
import Theorems.Thm_Lagrange_exists_multiplier

-- carved verbatim out of submission 3c55ced4-4944-4de2-ba43-8110d2682db1, lines 3808-3849

section
open MeasureTheory Matrix
open scoped ENNReal

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] (L h : E → ℝ)
    (hL : ConcaveOn ℝ Set.univ L) (hh : ConvexOn ℝ Set.univ h) (hslater : ∃ x₀, 0 < L x₀)
    (H : ∀ x, 0 ≤ L x → 0 ≤ h x) : ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ h x - τ * L x := by
  let K : PointedCone ℝ ℝ :=
    { carrier := {x | 0 ≤ x}
      add_mem' := fun {a b} ha hb => show 0 ≤ a + b from add_nonneg ha hb
      zero_mem' := show (0 : ℝ) ≤ 0 from le_refl (0 : ℝ)
      smul_mem' := fun c x hx => show (0 : ℝ) ≤ (c : ℝ) * x from mul_nonneg c.2 hx }
  have hcvx : ∀ x₁ ∈ (Set.univ : Set E), ∀ x₂ ∈ (Set.univ : Set E), ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ x ∈ (Set.univ : Set E), L x - (t • L x₁ + (1 - t) • L x₂) ∈ K ∧
        t * (-h x₁) + (1 - t) * (-h x₂) ≤ -h x := by
    intro x₁ _ x₂ _ t ht0 ht1
    refine ⟨t • x₁ + (1 - t) • x₂, Set.mem_univ _, ?_, ?_⟩
    · have := hL.2 (Set.mem_univ x₁) (Set.mem_univ x₂) ht0 (sub_nonneg.2 ht1)
        (by ring : t + (1 - t) = 1)
      exact show (0 : ℝ) ≤ _ from sub_nonneg.2 this
    · have := hh.2 (Set.mem_univ x₁) (Set.mem_univ x₂) ht0 (sub_nonneg.2 ht1)
        (by ring : t + (1 - t) = 1)
      simp only [smul_eq_mul] at this
      linarith
  have hsl : (0 : ℝ) ∈ interior {u | ∃ x ∈ (Set.univ : Set E), L x - u ∈ K} := by
    obtain ⟨x₀, hx₀⟩ := hslater
    rw [mem_interior]
    exact ⟨Set.Iio (L x₀), fun u (hu : u < L x₀) => ⟨x₀, Set.mem_univ _,
      show (0 : ℝ) ≤ L x₀ - u from sub_nonneg.2 (le_of_lt hu)⟩,
      isOpen_Iio, hx₀⟩
  have hp : ∀ x ∈ (Set.univ : Set E), L x ∈ K → -h x ≤ 0 := by
    intro x _ hx
    have := H x hx
    linarith
  obtain ⟨y, hyK, hy⟩ := Lagrange.exists_multiplier Set.univ (fun x => -h x) L K
    hcvx hsl 0 hp
  have e : ∀ x, y (L x) = L x * y 1 := by
    intro x; simpa using y.map_smul (L x) 1
  refine ⟨y 1, hyK 1 (show (0 : ℝ) ≤ 1 from zero_le_one), fun x => ?_⟩
  have := hy x (Set.mem_univ _)
  rw [e] at this
  linarith

end

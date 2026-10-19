-- Prove2me | solution 1 for SoficGroups.inner_sq_le_of_orthogonal_two_sector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/fe9b2403-e678-47a6-8241-e374092e1c4d

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups
theorem _root_.solution
    (a₀ a₁ b₀ b₁ : H)
    (ha : inner ℂ a₀ a₁ = 0)
    (hb : inner ℂ b₀ b₁ = 0)
    (hcross₀ : inner ℂ a₀ b₁ = 0)
    (hcross₁ : inner ℂ a₁ b₀ = 0)
    (h₀ : 8 * ‖inner ℂ a₀ b₀‖ ^ 2 ≤ ‖a₀‖ ^ 2 * ‖b₀‖ ^ 2)
    (h₁ : 8 * ‖inner ℂ a₁ b₁‖ ^ 2 ≤ ‖a₁‖ ^ 2 * ‖b₁‖ ^ 2) :
    8 * ‖inner ℂ (a₀ + a₁) (b₀ + b₁)‖ ^ 2 ≤
      ‖a₀ + a₁‖ ^ 2 * ‖b₀ + b₁‖ ^ 2 := by
  have hproduct :
      (8 * ‖inner ℂ a₀ b₀‖ * ‖inner ℂ a₁ b₁‖) ^ 2 ≤
        (‖a₀‖ * ‖a₁‖ * ‖b₀‖ * ‖b₁‖) ^ 2 := by
    calc
      (8 * ‖inner ℂ a₀ b₀‖ * ‖inner ℂ a₁ b₁‖) ^ 2 =
          (8 * ‖inner ℂ a₀ b₀‖ ^ 2) *
            (8 * ‖inner ℂ a₁ b₁‖ ^ 2) := by ring
      _ ≤ (‖a₀‖ ^ 2 * ‖b₀‖ ^ 2) *
          (‖a₁‖ ^ 2 * ‖b₁‖ ^ 2) :=
        mul_le_mul h₀ h₁ (by positivity) (by positivity)
      _ = (‖a₀‖ * ‖a₁‖ * ‖b₀‖ * ‖b₁‖) ^ 2 := by ring
  have hcross :
      8 * ‖inner ℂ a₀ b₀‖ * ‖inner ℂ a₁ b₁‖ ≤
        ‖a₀‖ * ‖a₁‖ * ‖b₀‖ * ‖b₁‖ :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hproduct
  have hscalar :
      8 * (‖inner ℂ a₀ b₀‖ + ‖inner ℂ a₁ b₁‖) ^ 2 ≤
        (‖a₀‖ ^ 2 + ‖a₁‖ ^ 2) *
          (‖b₀‖ ^ 2 + ‖b₁‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a₀‖ * ‖b₁‖ - ‖a₁‖ * ‖b₀‖)]
  have hinner :
      inner ℂ (a₀ + a₁) (b₀ + b₁) =
        inner ℂ a₀ b₀ + inner ℂ a₁ b₁ := by
    simp [hcross₀, hcross₁]
  have hnorm :
      ‖inner ℂ (a₀ + a₁) (b₀ + b₁)‖ ≤
        ‖inner ℂ a₀ b₀‖ + ‖inner ℂ a₁ b₁‖ := by
    rw [hinner]
    exact norm_add_le _ _
  have hnormsq :
      ‖inner ℂ (a₀ + a₁) (b₀ + b₁)‖ ^ 2 ≤
        (‖inner ℂ a₀ b₀‖ + ‖inner ℂ a₁ b₁‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have ha' : ‖a₀ + a₁‖ ^ 2 = ‖a₀‖ ^ 2 + ‖a₁‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), ha]
    simp
  have hb' : ‖b₀ + b₁‖ ^ 2 = ‖b₀‖ ^ 2 + ‖b₁‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), hb]
    simp
  rw [ha', hb']
  nlinarith
end SoficGroups

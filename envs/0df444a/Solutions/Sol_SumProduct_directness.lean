-- Prove2me | solution 1 for SumProduct.directness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:15.044992+00:00
-- url     : https://prove2.me/submissions/aad8b2a7-682f-4fdc-bf50-7dda7ca81e1d

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction
import Theorems.Thm_SumProduct_place_natCast
import Theorems.Thm_SumProduct_place_translate_bound
import Theorems.Thm_SumProduct_unit_separation


set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open Real
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {n : ℕ} {r : ℝ} (hrn : r < (n : ℝ))
    (hφ : ((n : ℝ) + r) / ((n : ℝ) - r) < goldenRatio)
    {g₁ g₂ : (𝓞 K)ˣ} {b₁ b₂ : 𝓞 K} (hb₁ : b₁ ∈ boxAdd K r) (hb₂ : b₂ ∈ boxAdd K r)
    (heq : (g₁ : 𝓞 K) * ((n : 𝓞 K) + b₁) = (g₂ : 𝓞 K) * ((n : 𝓞 K) + b₂)) :
    g₁ = g₂ ∧ b₁ = b₂ := by
  classical
  have hnr : (0 : ℝ) < (n : ℝ) - r := by linarith
  set u : (𝓞 K)ˣ := g₁⁻¹ * g₂ with hu
  -- `p₁ = u · p₂`.
  have hp : (n : 𝓞 K) + b₁ = (u : 𝓞 K) * ((n : 𝓞 K) + b₂) := by
    apply mul_left_cancel₀ (Units.ne_zero g₁)
    rw [heq]
    rw [← mul_assoc, ← Units.val_mul, hu, mul_inv_cancel_left]
  -- Every place of `u` lies in `(φ⁻¹, φ)`.
  have hu_sep : ∀ w : NumberField.InfinitePlace K,
      goldenRatio⁻¹ < w ((u : 𝓞 K) : K) ∧ w ((u : 𝓞 K) : K) < goldenRatio := by
    intro w
    obtain ⟨hp₁lo, hp₁hi⟩ := place_translate_bound w n hb₁
    obtain ⟨hp₂lo, hp₂hi⟩ := place_translate_bound w n hb₂
    have hp₂pos : 0 < w (((n : 𝓞 K) + b₂ : 𝓞 K) : K) := lt_of_lt_of_le hnr hp₂lo
    have hcoe : (((n : 𝓞 K) + b₁ : 𝓞 K) : K)
        = ((u : 𝓞 K) : K) * (((n : 𝓞 K) + b₂ : 𝓞 K) : K) := by
      rw [hp]; push_cast; ring
    have hwu : w ((u : 𝓞 K) : K)
        = w (((n : 𝓞 K) + b₁ : 𝓞 K) : K) / w (((n : 𝓞 K) + b₂ : 𝓞 K) : K) := by
      rw [eq_div_iff hp₂pos.ne', ← map_mul, ← hcoe]
    have hub : (n : ℝ) + r < goldenRatio * ((n : ℝ) - r) := (div_lt_iff₀ hnr).mp hφ
    rw [hwu]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hp₂pos]
      calc goldenRatio⁻¹ * w (((n : 𝓞 K) + b₂ : 𝓞 K) : K)
          ≤ goldenRatio⁻¹ * ((n : ℝ) + r) :=
            mul_le_mul_of_nonneg_left hp₂hi (le_of_lt (inv_pos.mpr goldenRatio_pos))
        _ < (n : ℝ) - r := by rw [inv_mul_lt_iff₀ goldenRatio_pos]; linarith [hub]
        _ ≤ w (((n : 𝓞 K) + b₁ : 𝓞 K) : K) := hp₁lo
    · rw [div_lt_iff₀ hp₂pos]
      calc w (((n : 𝓞 K) + b₁ : 𝓞 K) : K) ≤ (n : ℝ) + r := hp₁hi
        _ < goldenRatio * ((n : ℝ) - r) := hub
        _ ≤ goldenRatio * w (((n : 𝓞 K) + b₂ : 𝓞 K) : K) :=
            mul_le_mul_of_nonneg_left hp₂lo (le_of_lt goldenRatio_pos)
  rcases unit_separation K u hu_sep with h1 | h1
  · -- `u = 1`: `g₁ = g₂` and `b₁ = b₂`.
    have hgg : g₁⁻¹ * g₂ = 1 := by rw [← hu]; exact h1
    refine ⟨inv_mul_eq_one.mp hgg, ?_⟩
    have hu1 : (u : 𝓞 K) = 1 := by rw [h1]; rfl
    rw [hu1, one_mul] at hp
    exact add_left_cancel hp
  · -- `u = -1`: impossible.
    exfalso
    have hu1 : (u : 𝓞 K) = -1 := by rw [h1]; rfl
    rw [hu1, neg_one_mul] at hp
    have hsum : b₁ + b₂ = -(((n + n : ℕ)) : 𝓞 K) := by push_cast; linear_combination hp
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
    have hb₁' : w₀ (b₁ : K) ≤ r := (mem_boxAdd.mp hb₁) w₀
    have hb₂' : w₀ (b₂ : K) ≤ r := (mem_boxAdd.mp hb₂) w₀
    have hval : w₀ ((b₁ + b₂ : 𝓞 K) : K) = (n : ℝ) + n := by
      have hcoe : ((b₁ + b₂ : 𝓞 K) : K) = -(((n + n : ℕ) : K)) := by rw [hsum]; push_cast; ring
      have hneg : w₀ (-(((n + n : ℕ) : K))) = w₀ (((n + n : ℕ) : K)) := w₀.1.map_neg _
      rw [hcoe, hneg, place_natCast]; push_cast; ring
    have htri : w₀ ((b₁ + b₂ : 𝓞 K) : K) ≤ w₀ (b₁ : K) + w₀ (b₂ : K) := by
      have he : ((b₁ + b₂ : 𝓞 K) : K) = (b₁ : K) + (b₂ : K) := by push_cast; ring
      rw [he]; exact w₀.1.add_le _ _
    rw [hval] at htri
    linarith
end SumProduct

-- Prove2me | solution 1 for SumProduct.card_le_boxAdd_of_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:06:43.284723+00:00
-- url     : https://prove2.me/submissions/4c17f688-a150-4088-8658-302d2b45fbd6

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_abs_realEmbed
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (r : ℝ) (c : InfinitePlace K → ℝ) (T : Finset (𝓞 K))
    (hT : ∀ α ∈ T, ∀ w, |realEmbed K α w - c w| ≤ r) :
    T.card ≤ (boxAdd K (2 * r)).card := by
  rcases T.eq_empty_or_nonempty with hTe | ⟨α₀, hα₀⟩
  · simp [hTe]
  · refine Finset.card_le_card_of_injOn (fun α => α - α₀) ?_ ?_
    · intro α hα
      simp only [Finset.mem_coe, mem_boxAdd]
      intro w
      rw [← abs_realEmbed]
      have e : realEmbed K (α - α₀) w = realEmbed K α w - realEmbed K α₀ w := by
        simp only [realEmbed]
        rw [show ((α - α₀ : 𝓞 K) : K) = (α : K) - (α₀ : K) by push_cast; ring, map_sub]
      rw [e]
      calc |realEmbed K α w - realEmbed K α₀ w|
          ≤ |realEmbed K α w - c w| + |c w - realEmbed K α₀ w| := by
            rw [show realEmbed K α w - realEmbed K α₀ w
                = (realEmbed K α w - c w) + (c w - realEmbed K α₀ w) by ring]
            exact abs_add_le _ _
        _ ≤ r + r := by
            have h1 := hT α hα w
            have h2 := hT α₀ hα₀ w
            rw [abs_sub_comm (c w) (realEmbed K α₀ w)]
            linarith
        _ = 2 * r := by ring
    · intro α _ β _ h
      linear_combination h
end SumProduct

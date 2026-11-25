-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdB.posDef_nhd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:43.10525+00:00
-- url     : https://prove2.me/submissions/da098212-58e6-4104-b32d-0f4ffa5c79e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdB_quad_norm_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdB_quad_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdB
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdB
theorem _root_.solution {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ δ > 0, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → ‖H‖ < δ → (x + H).PosDef := by
  obtain ⟨c, hc, hq⟩ := quad_lower hx
  refine ⟨c / ((n : ℝ) * n + 1), by positivity, fun H hH hHn => ?_⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨hx.isHermitian.add hH, fun v hv => ?_⟩
  rw [Complex.lt_def]
  have him := (hx.isHermitian.add hH).im_star_dotProduct_mulVec_self v
  have e : star v ⬝ᵥ ((x + H) *ᵥ v) = star v ⬝ᵥ (x *ᵥ v) + star v ⬝ᵥ (H *ᵥ v) := by
    rw [add_mulVec, dotProduct_add]
  refine ⟨?_, ?_⟩
  · rw [e, Complex.add_re, Complex.zero_re]
    have h1 := hq v
    have h2 := quad_norm_le H v
    have h3 : -‖star v ⬝ᵥ (H *ᵥ v)‖ ≤ (star v ⬝ᵥ (H *ᵥ v)).re := by
      have := Complex.abs_re_le_norm (star v ⬝ᵥ (H *ᵥ v))
      linarith [neg_abs_le (star v ⬝ᵥ (H *ᵥ v)).re]
    have hv2 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.mpr hv; positivity
    have hN : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
    have hHpos : 0 ≤ ‖H‖ := norm_nonneg _
    have hδ : ((n : ℝ) * n + 1) * ‖H‖ < c := by
      rw [lt_div_iff₀ (by positivity)] at hHn
      linarith
    have h4 : 0 < (c - (n : ℝ) * n * ‖H‖) * ‖v‖ ^ 2 := mul_pos (by nlinarith) hv2
    nlinarith
  · rw [Complex.zero_im]
    simpa using him.symm
end ReciprocityTheory.ChartRestriction.DS.S7.IdB

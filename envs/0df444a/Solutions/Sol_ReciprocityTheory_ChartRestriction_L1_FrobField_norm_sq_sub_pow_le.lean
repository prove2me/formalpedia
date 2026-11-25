-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.FrobField.norm_sq_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:27.837978+00:00
-- url     : https://prove2.me/submissions/d29e74f2-d0ac-4448-be24-5da63e7bc70d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_semilin_norm_pow_sub_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
omit [CompleteSpace K] [CharZero K]
namespace ReciprocityTheory.ChartRestriction.L1
namespace FrobField
theorem _root_.solution {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (x : K) (hx : ‖x‖ ≤ 1) :
    ‖σ (σ x) - x ^ (l ^ 2)‖ ≤ ‖(l : K)‖ := by
  have hp : x ^ (l ^ 2) = (x ^ l) ^ l := by rw [← pow_mul, sq]
  have e : σ (σ x) - x ^ (l ^ 2) = σ (σ x - x ^ l) + ((σ x) ^ l - (x ^ l) ^ l) := by
    rw [hp, map_sub, map_pow]
    ring
  have h1 : ‖σ x - x ^ l‖ ≤ ‖(l : K)‖ := h.frob x hx
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [h.isom]; exact h1
  · refine (semilin_norm_pow_sub_pow (by rw [h.isom]; exact hx) ?_ l).trans h1
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
end FrobField
end ReciprocityTheory.ChartRestriction.L1

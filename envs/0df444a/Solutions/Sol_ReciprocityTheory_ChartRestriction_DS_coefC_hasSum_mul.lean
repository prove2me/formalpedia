-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefC_hasSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:57.571333+00:00
-- url     : https://prove2.me/submissions/6cb4a848-a0a8-43b0-82fe-d6322e063259

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefCExpEntrySummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {f g : ℕ → ℂ} {a b : ℂ} (hf : HasSum f a) (hg : HasSum g b)
    (hf' : Summable fun j => ‖f j‖) (hg' : Summable fun j => ‖g j‖) :
    HasSum (fun m => ∑ kl ∈ antidiagonal m, f kl.1 * g kl.2) (a * b) := by
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hf' hg'
  have h := (Summable.of_norm hs).hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf' hg', hf.tsum_eq, hg.tsum_eq] at h
  exact h
end ReciprocityTheory.ChartRestriction.DS

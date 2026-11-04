-- Prove2me | solution 1 for ThreeSum.Scales.candidateCount_eventually_gt_multiple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:45.016048+00:00
-- url     : https://prove2.me/submissions/a98ff212-50ac-4602-8968-17a0e194919f

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
import Theorems.Thm_ThreeSum_Scales_actual_candidates_nonempty
import Theorems.Thm_ThreeSum_Scales_bits_over_candidateCount_tendsto_zero
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * (inputBits n + 1) < candidateCount n := by
  have hsmall := bits_over_candidateCount_tendsto_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((K : ℝ) + 1)))
  filter_upwards [hsmall, actual_candidates_nonempty] with n hn hC
  have hCpos : (0 : ℝ) < candidateCount n := by
    exact_mod_cast Finset.card_pos.mpr hC
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have h := (div_lt_div_iff₀ hCpos hKpos).mp hn
  have hNat : (inputBits n + 1) * (K + 1) < candidateCount n := by
    simpa only [one_mul] using (show (inputBits n + 1 : ℝ) * ((K : ℝ) + 1) <
      candidateCount n by simpa only [one_mul] using h) |> fun ht => by exact_mod_cast ht
  nlinarith
end ThreeSum.Scales

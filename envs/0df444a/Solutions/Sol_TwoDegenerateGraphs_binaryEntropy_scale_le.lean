-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryEntropy_scale_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/e57d1332-baaf-484e-a910-e7503cb029e3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (probability scale : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hscale_zero : 0 ≤ scale)
    (hscale_one : scale ≤ 1) :
    scale * binaryEntropy probability ≤
      binaryEntropy (scale * probability) := by
  have hconcavity := Real.strictConcave_binEntropy.concaveOn.2
    (show probability ∈ Set.Icc (0 : ℝ) 1 from
      ⟨hprobability_zero, hprobability_one⟩)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    hscale_zero (sub_nonneg.mpr hscale_one)
    (show scale + (1 - scale) = 1 by ring)
  have hnatural :
      scale * Real.binEntropy probability ≤
        Real.binEntropy (scale * probability) := by
    simpa [smul_eq_mul] using hconcavity
  unfold binaryEntropy
  calc
    scale * (Real.binEntropy probability / Real.log 2) =
      (scale * Real.binEntropy probability) / Real.log 2 := by ring
    _ ≤ Real.binEntropy (scale * probability) / Real.log 2 :=
      (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural
end TwoDegenerateGraphs

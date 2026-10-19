-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryEntropy_mono_on_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/0e58db6d-62a0-49ed-8cf3-f8db689f75e8

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyhalf : y ≤ (2 : ℝ)⁻¹) :
    binaryEntropy x ≤ binaryEntropy y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hxhalf : x ≤ (2 : ℝ)⁻¹ := hxy.trans hyhalf
  have hnatural := Real.binEntropy_strictMonoOn.monotoneOn
    (show x ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hx, hxhalf⟩)
    (show y ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hy, hyhalf⟩)
    hxy
  unfold binaryEntropy
  exact (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural
end TwoDegenerateGraphs

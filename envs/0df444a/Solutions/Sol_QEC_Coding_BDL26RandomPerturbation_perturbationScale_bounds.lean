-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.perturbationScale_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:32.948535+00:00
-- url     : https://prove2.me/submissions/84f227a1-ee27-46cc-972b-305e36bc7193

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {alpha probabilityConstant : ℝ} (ha : 0 ≤ alpha) (D : ℕ) :
    1 ≤ perturbationScale alpha probabilityConstant D ∧
      13 ≤ (2 * alpha + 1) * perturbationScale alpha probabilityConstant D ∧
      4 * probabilityConstant * (D + 1) ≤ perturbationScale alpha probabilityConstant D := by
  have hp : 0 < 2 * alpha + 1 := by linarith
  have hfirst := le_max_left (1 : ℝ)
    (max (13 / (2 * alpha + 1)) (4 * probabilityConstant * (D + 1)))
  have hsecond := (le_max_left (13 / (2 * alpha + 1))
    (4 * probabilityConstant * (D + 1))).trans (le_max_right (1 : ℝ) _)
  have hthird := (le_max_right (13 / (2 * alpha + 1))
    (4 * probabilityConstant * (D + 1))).trans (le_max_right (1 : ℝ) _)
  refine ⟨hfirst, ?_, hthird⟩
  have hs := (div_le_iff₀ hp).mp hsecond
  simpa [perturbationScale, mul_comm] using hs
end QEC.Coding.BDL26RandomPerturbation

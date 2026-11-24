-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.cubeProj_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:35.172849+00:00
-- url     : https://prove2.me/submissions/bb9ef5f5-1880-4066-bcfd-852851829dcb

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.Osgood
open Complex Metric MeasureTheory Set Filter Topology
open scoped Real
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.Osgood
theorem _root_.solution {θ : Fin n → ℝ} (hθ : θ ∈ Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) :
    (cubeProj θ : Fin n → ℝ) = θ := by
  funext i
  show ((projIcc 0 (2 * π) Real.two_pi_pos.le (θ i) : ℝ)) = θ i
  have hi : θ i ∈ Icc (0 : ℝ) (2 * π) := ⟨hθ.1 i, hθ.2 i⟩
  rw [projIcc_of_mem _ hi]
end ReciprocityTheory.AnForm.Osgood

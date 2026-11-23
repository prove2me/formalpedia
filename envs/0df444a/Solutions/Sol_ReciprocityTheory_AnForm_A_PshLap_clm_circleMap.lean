-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.clm_circleMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:36.580194+00:00
-- url     : https://prove2.me/submissions/6b1e9aa8-ac23-460b-9cf3-d6a9648b1b69

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleMap_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (L : ℂ →L[ℝ] ℝ) (r θ : ℝ) :
    L (circleMap 0 r θ) = r * L (circleMap 0 1 θ) := by
  rw [circleMap_eq_smul r θ, map_smul, smul_eq_mul]
end ReciprocityTheory.AnForm.A.PshLap

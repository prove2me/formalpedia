-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_hd_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:25.491462+00:00
-- url     : https://prove2.me/submissions/43bbffa3-29b2-4b9c-b15c-a7209a32b1a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_hd_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f f' s) : HasDerivAt (fun t => (f t)ᴴ) f'ᴴ s := by
  refine slm_hd_iff.mpr fun i j => ?_
  have h1 := (slm_hd_iff.mp hf j i).star
  simpa [Matrix.conjTranspose_apply] using h1
end ReciprocityTheory.ChartRestriction.DS

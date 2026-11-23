-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_hd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:16.702796+00:00
-- url     : https://prove2.me/submissions/564501b5-f3d5-4f83-a3e3-980d66f3a64c

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
theorem _root_.solution {f g : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' g' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => f t * g t) (f' * g s + f s * g') s := by
  refine slm_hd_iff.mpr fun i j => ?_
  have hf' := slm_hd_iff.mp hf
  have hg' := slm_hd_iff.mp hg
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  first
  | exact HasDerivAt.fun_sum fun k _ => (hf' i k).mul (hg' k j)
  | exact HasDerivAt.sum fun k _ => (hf' i k).mul (hg' k j)
end ReciprocityTheory.ChartRestriction.DS

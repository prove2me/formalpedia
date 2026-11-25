-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.volume_bad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:52.415523+00:00
-- url     : https://prove2.me/submissions/89cdd9e4-dca1-46d7-9940-f3d968b2fc49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_volume_axes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (ι : Type*) [Fintype ι] :
    volume {x : ι → ℂ | ∃ i, (x i).im = 0 ∨ (x i).re = 0} = 0 := by
  have hs : {x : ι → ℂ | ∃ i, (x i).im = 0 ∨ (x i).re = 0} =
      ⋃ i, (fun x : ι → ℂ => x i) ⁻¹' {z : ℂ | z.im = 0 ∨ z.re = 0} := by
    ext x; simp
  rw [hs]
  refine measure_iUnion_null fun i => ?_
  rw [volume_pi]
  first
  | exact Measure.pi_eval_preimage_null _ volume_axes
  | exact Measure.pi_eval_preimage_null volume_axes
  | exact Measure.pi_eval_preimage_null (μ := fun _ => volume) volume_axes
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0

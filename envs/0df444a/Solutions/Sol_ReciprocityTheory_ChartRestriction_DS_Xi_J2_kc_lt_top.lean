-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.kc_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:27.020459+00:00
-- url     : https://prove2.me/submissions/15034655-a432-47b9-b791-316114c03ace

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {s : ℝ} (hs : 2 < s) : kc s < ∞ := by
  unfold kc
  have hi := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := (volume : Measure ℂ)) (r := s)
    (by rw [Complex.finrank_real_complex]; exact_mod_cast hs)
  exact hi.lintegral_lt_top
end ReciprocityTheory.ChartRestriction.DS.Xi.J2

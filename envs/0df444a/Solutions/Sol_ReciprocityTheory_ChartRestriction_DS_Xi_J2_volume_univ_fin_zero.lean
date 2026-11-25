-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.volume_univ_fin_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:35.160794+00:00
-- url     : https://prove2.me/submissions/8706e354-5039-4db2-aad0-1327dd9012dd

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
theorem _root_.solution : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1 := by
  first
  | simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  | (rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]; simp)
  | simp
end ReciprocityTheory.ChartRestriction.DS.Xi.J2

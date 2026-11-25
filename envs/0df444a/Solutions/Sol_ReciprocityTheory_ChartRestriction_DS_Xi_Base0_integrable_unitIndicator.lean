-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.integrable_unitIndicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:24.50149+00:00
-- url     : https://prove2.me/submissions/f5fe441b-a4c6-4cfe-9e54-8fe2d14e9521

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator

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
theorem _root_.solution : Integrable one1 := by
  unfold one1
  first
  | exact (continuous_one.integrableOn_Icc).integrable_indicator measurableSet_Icc
  | exact (Continuous.integrableOn_Icc continuous_const).integrable_indicator measurableSet_Icc
  | exact (integrableOn_const.2 (Or.inr measure_Icc_lt_top)).integrable_indicator measurableSet_Icc
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0

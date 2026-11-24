-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.enn_nnnorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:58:13.075798+00:00
-- url     : https://prove2.me/submissions/1e88eeea-8bf8-49d1-b9c5-bb8266074b28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (z : ℂ) : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  first
  | exact (ofReal_norm_eq_enorm z).symm
  | (rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (norm_nonneg _)]; rfl)
  | simp
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0

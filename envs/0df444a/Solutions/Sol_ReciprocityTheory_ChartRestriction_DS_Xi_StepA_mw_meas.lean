-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.mw_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:04:12.803962+00:00
-- url     : https://prove2.me/submissions/c9f4a1b9-2f2e-468c-a8f2-ecbfd3c0fa9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergFactsOfInductiveInput
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerCLe

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution : Measurable (mw k r') := by
  unfold mw
  exact (measurable_norm.pow_const _).min measurable_norm.inv
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA

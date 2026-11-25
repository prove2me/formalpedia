-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.haar_unique_of_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:56.703939+00:00
-- url     : https://prove2.me/submissions/6571bfac-201a-4c93-ab05-207082c518cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_UnitaryGroupStructuralFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_SharpIntegralGNOfStructuralFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
theorem _root_.solution (h : UnitaryGroupStructuralFacts) : HaarUnique := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

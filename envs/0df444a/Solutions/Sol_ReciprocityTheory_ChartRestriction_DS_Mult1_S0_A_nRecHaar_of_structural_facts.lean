-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.nRecHaar_of_structural_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:26.529477+00:00
-- url     : https://prove2.me/submissions/4d2c5145-688c-4a5e-afa0-465c3e40ff1a

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
theorem _root_.solution (h : UnitaryGroupStructuralFacts) : NRecHaar := by
  exact h.1.2.2.2.1
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

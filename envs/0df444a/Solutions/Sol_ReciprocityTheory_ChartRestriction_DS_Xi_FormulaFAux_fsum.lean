-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.fsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:58:03.99209+00:00
-- url     : https://prove2.me/submissions/537be696-89b5-48ba-9cf7-49b1e901d935

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula

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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
theorem _root_.solution (r' : ℕ) (g : ℕ → ℂ) : ∑ j : Fin (1 + r'), g j.val = ∑ j ∈ Finset.range (r' + 1), g j := by
  rw [Fin.sum_univ_eq_sum_range g (1 + r'), Nat.add_comm]
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.sh_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:58:12.066552+00:00
-- url     : https://prove2.me/submissions/6d1adf0c-3146-43be-967b-c54debd409ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec

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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (q : Fin (2 * r' + k + 1)) : (sh q).val = q.val + 1 := rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.BL

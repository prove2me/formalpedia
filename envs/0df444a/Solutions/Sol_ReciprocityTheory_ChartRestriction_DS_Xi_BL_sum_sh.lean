-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.sum_sh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:30.370803+00:00
-- url     : https://prove2.me/submissions/b59045d7-ef35-4a03-97ee-459add2c1e55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_sum_mid

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
theorem _root_.solution (f : Fin (2 * (1 + r') + k + 1) → ℂ) (h0 : ∀ q : Fin _, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin _, q.val = 2 * (1 + r') + k → f q = 0) : ∑ q, f q = ∑ q : Fin (2 * r' + k + 1), f (sh q) :=
  sum_mid (n := 2 * r' + k + 1) (by omega) f h0 (fun q hq => h1 q (by omega))
end ReciprocityTheory.ChartRestriction.DS.Xi.BL

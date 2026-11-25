-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.io_bvec_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:08.805138+00:00
-- url     : https://prove2.me/submissions/bbaccbe2-13d7-43cf-828f-a8ca4349a92b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_mv_bvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_io_out

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
theorem _root_.solution (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) :
    ιLev k 1 r' g *ᵥ bvec q = bvec q := by
  funext p; rw [mv_bvec, io_out g p q hq]; unfold bvec; simp only [Pi.single_apply]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL

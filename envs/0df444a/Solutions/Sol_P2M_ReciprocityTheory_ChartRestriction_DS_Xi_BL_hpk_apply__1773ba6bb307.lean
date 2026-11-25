-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_apply__1773ba6bb307
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:15.928311+00:00
-- url     : https://prove2.me/submissions/67b0b776-9948-46ea-a893-f3f155d9807a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_apply

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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (k r i : ℕ) (hi : i < 2 * r + k + 1) (j : Fin (2 * r + k + 1)) :
    Hpk k r ⟨i, hi⟩ j = if j.val = sg k r i then (if i = r + k then -1 else 1) else 0 :=
  hpk_apply k r ⟨i, hi⟩ j
end ReciprocityTheory.ChartRestriction.DS.Xi.BL

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:38.974135+00:00
-- url     : https://prove2.me/submissions/2be58f07-5bbf-4cbd-b135-c909e1e49c08

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
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Hpk k r j i = Hpk k r i j := by
  rw [hpk_apply, hpk_apply]; unfold sg
  split_ifs <;> first | rfl | omega
end ReciprocityTheory.ChartRestriction.DS.Xi.BL

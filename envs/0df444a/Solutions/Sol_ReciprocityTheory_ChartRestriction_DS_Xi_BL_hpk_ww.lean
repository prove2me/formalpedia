-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_ww
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:13.824239+00:00
-- url     : https://prove2.me/submissions/21fca9b4-aa39-49d8-8c93-933e9fb7958e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
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
variable (k n : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (j j' : Fin (k + 1)) :
    Hpk k n (wI k n j) (wI k n j') = if j = j' then (if j.val = k then -1 else 1) else 0 := by
  rw [hpk_apply]
  have hj := j.2
  have e1 : (wI k n j).val = n + j.val := rfl
  have e2 : (wI k n j').val = n + j'.val := rfl
  have hs : sg k n (n + j.val) = n + j.val := by unfold sg; rw [if_neg (by omega)]
  rw [e1, e2, hs]
  by_cases h : j = j'
  · subst h; rw [if_pos rfl, if_pos rfl]
    by_cases h' : j.val = k
    · rw [if_pos (by omega : n + j.val = n + k), if_pos h']
    · rw [if_neg (by omega : ¬ n + j.val = n + k), if_neg h']
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by omega)))]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL

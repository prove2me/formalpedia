-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:17:24.755043+00:00
-- url     : https://prove2.me/submissions/f99448d6-a8e6-4ca2-94e1-96b00325c3ca

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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = sg k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  unfold Hpk sg
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    rcases h1 with h1 | h1
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_pos ⟨h1, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_neg (by omega), if_pos ⟨by omega, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1]
    push Not at h1
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h2 : i = j
    · subst h2; rw [if_pos ⟨h1.1, h1.2, rfl⟩, if_pos rfl]
    · rw [if_neg (fun h => h2 h.2.2), if_neg (fun h => h2 (Fin.ext h.symm))]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL

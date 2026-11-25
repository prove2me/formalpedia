-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.vogDrop_cardSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:56.6838+00:00
-- url     : https://prove2.me/submissions/25c25a80-ccbf-4ff8-9b47-fe4dec94c9c6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_CasOnLowStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_VogDrop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution {n : ℕ} (p : Fin n → Prop) (q : Fin n → Prop) [DecidablePred p] [DecidablePred q] :
    ((univ.filter fun x => p x ∧ q x).card : ℝ) + ((univ.filter fun x => p x ∧ ¬ q x).card : ℝ)
      = ((univ.filter p).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not (s := univ.filter p) q
  rw [Finset.filter_filter, Finset.filter_filter] at h
  exact_mod_cast h
end ReciprocityTheory.ChartRestriction.DS.Lap

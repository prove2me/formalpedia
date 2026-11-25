-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.vogDrop_rhoSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:43.397813+00:00
-- url     : https://prove2.me/submissions/236dadd4-4615-49ce-961e-6d5708c580fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_CasOnLowStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_VogDrop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_vogDrop_cardSplit

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    rhoC ε a + rhoN ε a = ((n : ℝ) - 1 - 2 * (a : ℕ)) / 2 := by
  have h1 := vogDrop_cardSplit (fun b => a < b) (fun b => ε b = ε a)
  have h2 := vogDrop_cardSplit (fun b => b < a) (fun b => ε b = ε a)
  have ha := a.isLt
  have e1 : ((univ.filter fun b : Fin n => a < b).card : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    have hI : (univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
    rw [hI, Fin.card_Ioi, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have e2 : ((univ.filter fun b : Fin n => b < a).card : ℝ) = (a : ℕ) := by
    have hI : (univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
    rw [hI, Fin.card_Iio]
  simp only [rhoC, rhoN, ne_eq] at *
  rw [e1] at h1
  rw [e2] at h2
  linarith
end ReciprocityTheory.ChartRestriction.DS.Lap

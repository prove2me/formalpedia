-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.vogDrop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:20.537478+00:00
-- url     : https://prove2.me/submissions/be05c592-a5a6-4d4e-a724-0aab35df5cb3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_CasOnLowStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_VogDrop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_vogDrop_rhoSum

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
theorem _root_.solution (n : ℕ) : VogDropStatement n := by
  intro ε lam hlam a b hab _
  have hab' : a ≠ b := ne_of_lt hab
  set w : Fin n → ℝ := fun i => lam i + rhoN ε i + rhoC ε i with hw
  have key : vogSq ε (lowK ε lam - root a b) - vogSq ε (lowK ε lam) = 2 - 2 * (w a - w b) := by
    simp only [vogSq, nsq, dot, lowK, root]
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add a b hab']
    · simp [Pi.single_apply, hab', hab'.symm, w]
      ring
    · rintro x ⟨hxa, hxb⟩
      simp [Pi.single_apply, hxa, hxb]
  have hw_ab : w a - w b = (lam a - lam b) + (((b : ℕ) : ℝ) - (a : ℕ)) := by
    have ha := vogDrop_rhoSum ε a
    have hb := vogDrop_rhoSum ε b
    simp only [w]
    linarith
  have h1 : lam b < lam a := hlam hab
  have h2 : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by
    have : (a : ℕ) < b := Fin.lt_iff_val_lt_val.mp hab
    exact_mod_cast this
  linarith
end ReciprocityTheory.ChartRestriction.DS.Lap

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.prod_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:03.891857+00:00
-- url     : https://prove2.me/submissions/7038acfa-eafa-46ea-8395-333ee785a8e6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p : ℕ} (d s ν : Fin (p + 1) → ℝ) (hd : ∀ l, 0 < d l) (α : ℝ) :
    ∏ l, d l ^ (-(s l + Function.update ν 0 (α + ν 0) l)) = d 0 ^ (-α) * ∏ l, d l ^ (-(s l + ν l)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _)]
  rw [show -(s 0 + (α + ν 0)) = -α + -(s 0 + ν 0) by ring, Real.rpow_add (hd 0)]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.J2

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.formV_sub_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:57.213705+00:00
-- url     : https://prove2.me/submissions/8e1a3ea5-edb4-48e1-b038-e4d4f1d9331c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExistsCyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution {m r : ℕ} (u w : Fin m → ℝ) (k : Fin r → ℝ) (g : Fin r → Fin m → ℝ) :
    formV (fun s => u s - ∑ b, k b * g b s) w = formV u w - ∑ b, k b * formV (g b) w := by
  simp only [formV, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun s _ => by ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

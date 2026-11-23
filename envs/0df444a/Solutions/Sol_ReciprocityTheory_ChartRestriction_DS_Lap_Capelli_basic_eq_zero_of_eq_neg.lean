-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.basic_eq_zero_of_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:42.405353+00:00
-- url     : https://prove2.me/submissions/21e38829-00a5-451e-926f-38e88d31cca4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {𝒰 : Type*} [AddCommGroup 𝒰] [Module ℂ 𝒰] (c : 𝒰)
    (h : c = ((-1 : ℤˣ) : ℤ) • c) : c = 0 := by
  have h' : c = -c := by
    first
    | (rw [Units.val_neg, Units.val_one, neg_one_smul] at h; exact h)
    | (simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h; exact h)
  have h2 : (2 : ℂ) • c = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h']
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.permIns_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:09.706586+00:00
-- url     : https://prove2.me/submissions/400554be-0972-47e3-bd05-ce0b84cc70a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_permIns_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_permIns_succ

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
theorem _root_.solution {p : ℕ} :
    Function.Bijective (fun q : Fin (p + 1) × Equiv.Perm (Fin p) => permIns q.1 q.2) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨i, τ⟩ ⟨i', τ'⟩ h
    have h' : permIns i τ = permIns i' τ' := h
    have hi : i = i' := by
      have h0 := congrArg (fun σ : Equiv.Perm (Fin (p + 1)) => σ 0) h'
      simpa only [permIns_zero] using h0
    subst hi
    have hτ : τ = τ' := by
      refine Equiv.ext fun j => ?_
      have hj := congrArg (fun σ : Equiv.Perm (Fin (p + 1)) => σ j.succ) h'
      simp only [permIns_succ] at hj
      first
      | exact Fin.succAbove_right_injective hj
      | exact Fin.succAbove_right_inj.mp hj
    rw [hτ]
  · simp [Fintype.card_perm, Nat.factorial_succ]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

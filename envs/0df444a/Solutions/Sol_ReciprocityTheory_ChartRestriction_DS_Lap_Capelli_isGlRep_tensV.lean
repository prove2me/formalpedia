-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.isGlRep_tensV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:35.568553+00:00
-- url     : https://prove2.me/submissions/1598434b-844d-438a-820a-cfae4945bc7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Tensor
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensV_apply__cffaa40c8d7b

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) :
    IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have h := LinearMap.congr_fun (hE a b c d) (f e)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, tensV_apply', map_add, Pi.sub_apply]
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp only [hbc, hda, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensV_apply'] at h ⊢ <;>
    split_ifs <;> simp_all <;> (rw [← sub_eq_zero] at h ⊢; convert h using 1; abel)
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

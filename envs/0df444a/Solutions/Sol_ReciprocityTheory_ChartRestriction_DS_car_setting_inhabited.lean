-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.car_setting_inhabited
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:36.913942+00:00
-- url     : https://prove2.me/submissions/4506c027-2f69-4de6-bfff-67a8d7aed8b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isCAR_fock

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution :
    IsGlRep (0 : Fin n → Fin n → Module.End ℂ (Fock n)) ∧ IsCAR (cpFock (n := n)) cmFock ∧
      CommutesCAR (0 : Fin n → Fin n → Module.End ℂ (Fock n)) cpFock cmFock := by
  refine ⟨fun a b c d => ?_, isCAR_fock, fun a b i j => ?_⟩
  · simp
  · simp
end ReciprocityTheory.ChartRestriction.DS

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uq_mem_kSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:58.316117+00:00
-- url     : https://prove2.me/submissions/0ea42a9d-c067-4809-b067-e8ec43694bcf

import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (x : V) : x ∈ kSpan ε F x := by
    unfold kSpan
    exact Submodule.mem_sInf.2 fun _ hS => hS.1
end ReciprocityTheory.ChartRestriction.DS.HW

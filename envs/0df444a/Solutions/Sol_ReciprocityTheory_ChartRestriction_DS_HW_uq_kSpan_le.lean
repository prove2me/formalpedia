-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uq_kSpan_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:36:18.896552+00:00
-- url     : https://prove2.me/submissions/814932fa-ba99-4583-aff6-a2f72e4509f4

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
theorem _root_.solution {x : V} {S : Submodule ℂ V} (hx : x ∈ S) (hS : KStable ε F S) : kSpan ε F x ≤ S := by
    unfold kSpan
    exact sInf_le ⟨hx, hS⟩
end ReciprocityTheory.ChartRestriction.DS.HW

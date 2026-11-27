-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.commute_casimirK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:09.763204+00:00
-- url     : https://prove2.me/submissions/54931df2-edee-44f0-9c0f-a415ebb1fdcf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution {A : Fin n → Fin n → Module.End ℂ X} {Z : Module.End ℂ X}
    (h : ∀ c d, Commute Z (A c d)) : Commute Z (casimirK ε A) := by
  unfold casimirK
  exact Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => (h a b).mul_right (h b a)
end ReciprocityTheory.ChartRestriction.DS.BigCasimir

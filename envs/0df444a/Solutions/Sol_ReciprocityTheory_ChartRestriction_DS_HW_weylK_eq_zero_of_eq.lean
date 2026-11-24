-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylK_eq_zero_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:07.077706+00:00
-- url     : https://prove2.me/submissions/dbd922fc-ef61-4e56-ab86-ca831eba604a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) (hε : ε a = ε b)
    (h : (μ + rhoC ε) a = (μ + rhoC ε) b) : weylK ε μ = 0 := by
  unfold weylK
  refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
  refine Finset.prod_eq_zero (i := b) (Finset.mem_filter.2 ⟨Finset.mem_univ b, hab, hε⟩) ?_
  rw [h, sub_self, zero_div]
end ReciprocityTheory.ChartRestriction.DS.HW

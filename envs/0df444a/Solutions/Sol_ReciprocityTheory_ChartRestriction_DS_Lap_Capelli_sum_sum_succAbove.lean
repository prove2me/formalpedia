-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.sum_sum_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:31.850379+00:00
-- url     : https://prove2.me/submissions/01cd9930-d2a0-42c5-af2c-5dcb678a78ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA

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
theorem _root_.solution {M : Type*} [AddCommGroup M] {p : ℕ} (f : Fin (p + 1) → M) :
    ∑ i : Fin (p + 1), ∑ t : Fin p, f (i.succAbove t) = p • ∑ s, f s := by
  have h : ∀ i : Fin (p + 1), ∑ t : Fin p, f (i.succAbove t) = ∑ s, f s - f i := by
    intro i
    rw [Fin.sum_univ_succAbove f i]
    abel
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [succ_nsmul]
  abel
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

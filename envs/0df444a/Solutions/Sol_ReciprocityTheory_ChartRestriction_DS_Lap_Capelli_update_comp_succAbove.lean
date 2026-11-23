-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.update_comp_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:50.429675+00:00
-- url     : https://prove2.me/submissions/835d5eb8-3bde-4bf4-bd4d-1fa448210d15

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
theorem _root_.solution {α : Type*} {p : ℕ} (f : Fin (p + 1) → α) (i : Fin (p + 1)) (t : Fin p) :
    Function.update (f ∘ i.succAbove) t (f i) = f ∘ Equiv.swap i (i.succAbove t) ∘ i.succAbove := by
  funext u
  by_cases hu : u = t
  · subst hu
    simp
  · simp only [Function.update_apply, if_neg hu, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne i u)
      (fun h => hu (Fin.succAbove_right_injective h))]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelli_whittaker_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:41.699881+00:00
-- url     : https://prove2.me/submissions/b0a5f760-39c2-4d25-af8f-b46d142148f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_intertwine


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
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (k : ℕ) (E : Fin (k + 1) → Fin (k + 1) → Module.End ℂ M)
    (D : Fin k → Fin k → Module.End ℂ R) (l : M →ₗ[ℂ] R) (x : ℂ)
    (hD : ∀ i j, l ∘ₗ E (Fin.castSucc i) (Fin.castSucc j) = D i j ∘ₗ l) :
    l ∘ₗ cminor E Fin.castSucc Fin.castSucc x = capelliC D x ∘ₗ l :=
  cminor_intertwine E D Fin.castSucc (Fin.castSucc_injective k) l hD id id x
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

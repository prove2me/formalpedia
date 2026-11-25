-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_update_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:41.700018+00:00
-- url     : https://prove2.me/submissions/bae3009d-bb85-444d-bbec-c5d3cb298e36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_exists_perm_swap_succAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_update_comp_succAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_perm_rows


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
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {p : ℕ} (R : Fin (p + 1) → Fin n) (C : Fin p → Fin n) (i : Fin (p + 1))
    (t : Fin p) (y : ℂ) :
    cminor E (Function.update (R ∘ i.succAbove) t (R i)) C y =
      ((-1 : ℂ) ^ ((i : ℕ) + (i.succAbove t : ℕ) + 1)) • cminor E (R ∘ (i.succAbove t).succAbove) C y := by
  obtain ⟨π, hπ, hmap⟩ := exists_perm_swap_succAbove i (i.succAbove t) (Fin.succAbove_ne i t).symm
  have hrows : Function.update (R ∘ i.succAbove) t (R i) = (R ∘ (i.succAbove t).succAbove) ∘ π := by
    rw [update_comp_succAbove]
    funext u
    simp [hmap]
  rw [hrows, cminor_perm_rows, hπ, ← Int.cast_smul_eq_zsmul ℂ]
  simp
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

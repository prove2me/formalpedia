-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_update_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:19.411181+00:00
-- url     : https://prove2.me/submissions/4600133d-1c42-4842-89b1-50c09bf1bdd9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_exists_perm_swap_succAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_update_comp_succAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_perm_cols


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
theorem _root_.solution (hE : GlRelR E) {p : ℕ} (R : Fin p → Fin n) (C : Fin (p + 1) → Fin n)
    (j : Fin (p + 1)) (t : Fin p) (y : ℂ) :
    cminor E R (Function.update (C ∘ j.succAbove) t (C j)) y =
      ((-1 : ℂ) ^ ((j : ℕ) + (j.succAbove t : ℕ) + 1)) • cminor E R (C ∘ (j.succAbove t).succAbove) y := by
  obtain ⟨π, hπ, hmap⟩ := exists_perm_swap_succAbove j (j.succAbove t) (Fin.succAbove_ne j t).symm
  have hcols : Function.update (C ∘ j.succAbove) t (C j) = (C ∘ (j.succAbove t).succAbove) ∘ π := by
    rw [update_comp_succAbove]
    funext u
    simp [hmap]
  rw [hcols, cminor_perm_cols E hE, hπ, ← Int.cast_smul_eq_zsmul ℂ]
  simp
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

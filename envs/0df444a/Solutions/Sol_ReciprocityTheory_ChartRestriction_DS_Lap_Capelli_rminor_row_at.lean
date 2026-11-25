-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.rminor_row_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:49.468694+00:00
-- url     : https://prove2.me/submissions/53af859d-9f5c-4122-ba1d-b97ab68ec41b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_shiftedEntry_op
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_columnMinor_op_rev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_rowMinor_eq_unop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_neg_one_pow_add_rev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_col_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_glRelR_op


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
theorem _root_.solution (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (i : Fin (p + 1)) (x : ℂ) :
    rminor E R C x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
      (rminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) * capEntry E x (R i) (C j)) := by
  have hunop : ∀ g : Fin (p + 1) → 𝒰ᵐᵒᵖ,
      MulOpposite.unop (∑ i, g i) = ∑ i, MulOpposite.unop (g i) :=
    fun g => map_sum (MulOpposite.opAddEquiv : 𝒰 ≃+ 𝒰ᵐᵒᵖ).symm g _
  rw [rowMinor_eq_unop, cminor_col_at (hE := glRelR_op (hE := hE)) _ _ _ (Fin.rev i), hunop]
  refine Fintype.sum_equiv (Fin.revPerm (n := p + 1)) _ _ (fun i' => ?_)
  have e1 : (C ∘ Fin.rev) ∘ i'.succAbove = (C ∘ (Fin.rev i').succAbove) ∘ Fin.rev := by
    funext k
    simp [Fin.rev_succAbove]
  have e2 : (R ∘ Fin.rev) ∘ (Fin.rev i).succAbove = (R ∘ i.succAbove) ∘ Fin.rev := by
    funext k
    simp [Fin.rev_succAbove]
  rw [MulOpposite.unop_smul, MulOpposite.unop_mul, e1, e2, columnMinor_op_rev, MulOpposite.unop_op]
  simp only [Function.comp_apply, shiftedEntry_op, MulOpposite.unop_op, Fin.rev_rev, Fin.revPerm_apply]
  rw [neg_one_pow_add_rev]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

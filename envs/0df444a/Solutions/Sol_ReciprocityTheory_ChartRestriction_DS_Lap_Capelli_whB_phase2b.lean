-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_phase2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:37:39.718032+00:00
-- url     : https://prove2.me/submissions/e6a5238d-b5d3-430c-90d5-98bccb5aa099

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_l_cminor_firstrow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_seg_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_seg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_seg_castSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_g_eq

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
variable (k r : ℕ) (E : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → Module.End ℂ M)
  (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) (l : M →ₗ[ℂ] R) (hE : IsGlRep E)
  (hl : ∀ a b, blk k r a < blk k r b → l ∘ₗ E a b = ψ a b • l)
  (hψ : ∀ a b, blk k r a < blk k r b → ¬ IsSimplePair k r a b → ψ a b = 0)
include hE hl hψ
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (hr : 0 < r) (y : ℂ) :
    l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) (r - 1) (k + 1)) (whB_seg (k + 2 * r + 1) r (k + 1)) y =
      ((-1) ^ k * whB_g k r ψ (whB_c (k + 2 * r + 1) (r - 1))) •
        (l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) r k) (whB_seg (k + 2 * r + 1) r k) y) := by
  have hb0 : r - 1 + (k + 1) ≤ k + 2 * r + 1 := by omega
  have hb1 : r + (k + 1) ≤ k + 2 * r + 1 := by omega
  have hC : ∀ c : Fin (k + 1), blk k r (whB_seg (k + 2 * r + 1) (r - 1) (k + 1) 0) <
      blk k r (whB_seg (k + 2 * r + 1) r (k + 1) c) := by
    intro c; have := c.isLt
    simp only [blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
    split_ifs <;> omega
  refine (l_cminor_firstrow E hE (blk k r) ψ l hl _ _ y hC).trans ?_
  rw [Finset.sum_eq_single (Fin.last k)]
  · have hs' : IsSimplePair k r (whB_seg (k + 2 * r + 1) (r - 1) (k + 1) 0)
        (whB_seg (k + 2 * r + 1) r (k + 1) (Fin.last k)) := by
      simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero, Fin.val_last]
      split_ifs <;> omega
    rw [← whB_g_eq ψ hs', Fin.succAbove_last, whB_seg_castSucc, whB_seg_succ, Fin.val_last,
      Nat.sub_add_cancel hr]
    have e3 : whB_seg (k + 2 * r + 1) (r - 1) (k + 1) 0 = (whB_c (k + 2 * r + 1) (r - 1)) := by
      simp [whB_seg]
    rw [e3]
  · intro c _ hc
    have hcv : (c : ℕ) < k := by
      have := c.isLt
      have : (c : ℕ) ≠ k := fun h => hc (Fin.ext (by simp [h]))
      omega
    rw [hψ _ _ (hC c) ?_, mul_zero, zero_smul]
    simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
    split_ifs <;> omega
  · simp
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

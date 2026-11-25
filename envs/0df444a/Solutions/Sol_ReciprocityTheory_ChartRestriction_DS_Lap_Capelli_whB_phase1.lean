-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_phase1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:40.348714+00:00
-- url     : https://prove2.me/submissions/e48c459d-7842-476c-af2c-86e07884b680

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_l_cminor_lastcol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_seg_val
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
theorem _root_.solution (m : ℕ) (hm : m ≤ r) (y : ℂ) :
    l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) 0 (k + r + m)) (whB_seg (k + 2 * r + 1) 1 (k + r + m)) y =
      (∏ j ∈ range m, whB_g k r ψ (whB_c (k + 2 * r + 1) (k + r + j))) •
        (l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) 0 (k + r)) (whB_seg (k + 2 * r + 1) 1 (k + r))
          (y - m)) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    have hb0 : 0 + (k + r + m + 1) ≤ k + 2 * r + 1 := by omega
    have hb1 : 1 + (k + r + m + 1) ≤ k + 2 * r + 1 := by omega
    have hR : ∀ i : Fin (k + r + m + 1), blk k r (whB_seg (k + 2 * r + 1) 0 (k + r + m + 1) i) <
        blk k r (whB_seg (k + 2 * r + 1) 1 (k + r + m + 1) (Fin.last (k + r + m))) := by
      intro i
      have := i.isLt
      simp only [blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_last]
      split_ifs <;> omega
    have key := l_cminor_lastcol E hE (blk k r) ψ l hl _ _ y hR
    refine key.trans ?_
    rw [Finset.sum_eq_single (Fin.last (k + r + m))]
    · have hs : IsSimplePair k r (whB_seg (k + 2 * r + 1) 0 (k + r + m + 1) (Fin.last (k + r + m)))
          (whB_seg (k + 2 * r + 1) 1 (k + r + m + 1) (Fin.last (k + r + m))) := by
        simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_last]
        split_ifs <;> omega
      rw [← whB_g_eq ψ hs, Fin.succAbove_last, whB_seg_castSucc, whB_seg_castSucc, ih (by omega) (y - 1),
        smul_smul, Finset.prod_range_succ]
      have e : y - 1 - (m : ℂ) = y - ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      have e2 : (-1 : ℂ) ^ ((Fin.last (k + r + m) : ℕ) + (k + r + m)) = 1 := by
        rw [Fin.val_last]; exact Even.neg_one_pow ⟨_, rfl⟩
      have e3 : whB_seg (k + 2 * r + 1) 0 (k + r + m + 1) (Fin.last (k + r + m)) =
          (whB_c (k + 2 * r + 1) (k + r + m)) := by
        simp [whB_seg]
      rw [e, e2, e3, one_mul, mul_comm]
    · intro i _ hi
      have hiv : (i : ℕ) < k + r + m := by
        have := i.isLt
        have : (i : ℕ) ≠ k + r + m := fun h => hi (Fin.ext (by simp [h]))
        omega
      rw [hψ _ _ (hR i) ?_, mul_zero, zero_smul]
      simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_last]
      split_ifs <;> omega
    · simp
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

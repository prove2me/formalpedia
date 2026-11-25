-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_phase2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:27:02.116648+00:00
-- url     : https://prove2.me/submissions/53224de7-7071-4017-82f9-416a9dd213d7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_l_cminor_firstrow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_seg_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_seg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_cminor_cast
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
theorem _root_.solution (j : ℕ) : ∀ (s : ℕ), s + j + 1 = r → ∀ y : ℂ,
    l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) s (k + j + 1)) (whB_seg (k + 2 * r + 1) (s + 1) (k + j + 1)) y =
      (∏ i ∈ range j, whB_g k r ψ (whB_c (k + 2 * r + 1) (s + i))) •
        (l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) (r - 1) (k + 1)) (whB_seg (k + 2 * r + 1) r (k + 1)) y) := by
  induction j with
  | zero =>
    intro s hs y
    rw [Finset.prod_range_zero, one_smul,
      whB_cminor_cast E rfl (show s = r - 1 by omega) (show s + 1 = r by omega)]
  | succ j ih =>
    intro s hs y
    have hb0 : s + (k + j + 1 + 1) ≤ k + 2 * r + 1 := by omega
    have hb1 : s + 1 + (k + j + 1 + 1) ≤ k + 2 * r + 1 := by omega
    have hC : ∀ c : Fin (k + j + 1 + 1), blk k r (whB_seg (k + 2 * r + 1) s (k + j + 1 + 1) 0) <
        blk k r (whB_seg (k + 2 * r + 1) (s + 1) (k + j + 1 + 1) c) := by
      intro c
      have := c.isLt
      simp only [blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
      split_ifs <;> omega
    have key := l_cminor_firstrow E hE (blk k r) ψ l hl _ _ y hC
    refine key.trans ?_
    rw [Finset.sum_eq_single (0 : Fin (k + j + 1 + 1))]
    · have hs' : IsSimplePair k r (whB_seg (k + 2 * r + 1) s (k + j + 1 + 1) 0)
          (whB_seg (k + 2 * r + 1) (s + 1) (k + j + 1 + 1) 0) := by
        simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
        split_ifs <;> omega
      rw [← whB_g_eq ψ hs', Fin.succAbove_zero, whB_seg_succ, whB_seg_succ, ih (s + 1) (by omega) y,
        smul_smul, Finset.prod_range_succ']
      have e3 : whB_seg (k + 2 * r + 1) s (k + j + 1 + 1) 0 = (whB_c (k + 2 * r + 1) (s)) := by
        simp [whB_seg]
      have hp : ∏ i ∈ range j, whB_g k r ψ (whB_c (k + 2 * r + 1) (s + 1 + i)) =
          ∏ i ∈ range j, whB_g k r ψ (whB_c (k + 2 * r + 1) (s + (i + 1))) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [show s + 1 + i = s + (i + 1) by ring]
      rw [e3, hp, Fin.val_zero, pow_zero, one_mul, add_zero, mul_comm]
    · intro c _ hc
      have hcv : 0 < (c : ℕ) := by
        rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
        · exact absurd (Fin.ext (by simp [h])) hc
        · exact h
      rw [hψ _ _ (hC c) ?_, mul_zero, zero_smul]
      have := c.isLt
      simp only [IsSimplePair, inW, blk, whB_seg_val hb0, whB_seg_val hb1, Fin.val_zero]
      split_ifs <;> omega
    · simp
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

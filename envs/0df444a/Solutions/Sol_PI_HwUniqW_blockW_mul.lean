-- Prove2me | solution 1 for PI.HwUniqW.blockW_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:51.886682+00:00
-- url     : https://prove2.me/submissions/60014614-21bc-43db-bd0d-dae5f0fa8262

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_inB_bl
import Theorems.Thm_PI_HwUniqW_blockIndex_injective
import Theorems.Thm_PI_HwUniqW_mk_bl
import Theorems.Thm_PI_HwUniqW_block_mk
import Theorems.Thm_PI_HwUniqW_blockW_in
import Theorems.Thm_PI_HwUniqW_blockW_in_out
import Theorems.Thm_PI_HwUniqW_blockW_out

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution (a b : Matrix (Fin k) (Fin k) ℂ) :
    blockW k r a * blockW k r b = blockW k r (a * b) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : InB k r i
  · have key : ∑ l, blockW k r a i l * blockW k r b l j
        = ∑ c : Fin k, blockW k r a i (bl k r c) * blockW k r b (bl k r c) j := by
      have hm := Finset.sum_map (Finset.univ : Finset (Fin k)) ⟨bl k r, blockIndex_injective⟩
        (fun l => blockW k r a i l * blockW k r b l j)
      simp only [Function.Embedding.coeFn_mk] at hm
      rw [← hm]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro l _ hl
      have hl' : ¬ InB k r l := by
        intro h'
        apply hl
        have h'' : r ≤ l.val ∧ l.val < r + k := h'
        simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
        exact ⟨⟨l.val - r, by omega⟩, block_mk h' _⟩
      rw [blockW_in_out a hi hl', zero_mul]
    rw [key]
    by_cases hj : InB k r j
    · rw [blockW_in (a * b) hi hj, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro c _
      rw [blockW_in a hi (inB_bl c), blockW_in b (inB_bl c) hj]
      simp only [mk_bl]
    · rw [blockW_in_out (a * b) hi hj]
      apply Finset.sum_eq_zero
      intro c _
      rw [blockW_in_out b (inB_bl c) hj, mul_zero]
  · rw [blockW_out (a * b) hi, Finset.sum_eq_single i]
    · rw [blockW_out a hi, if_pos rfl, one_mul]
      exact blockW_out b hi
    · intro l _ hl
      rw [blockW_out a hi, if_neg (Ne.symm hl), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
end PI.HwUniqW

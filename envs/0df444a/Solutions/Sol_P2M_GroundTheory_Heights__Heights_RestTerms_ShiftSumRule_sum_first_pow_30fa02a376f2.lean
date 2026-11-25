-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_sum_first_pow_30fa02a376f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:03.646827+00:00
-- url     : https://prove2.me/submissions/a678aacd-65cc-42e6-b600-bf2f8eca8296

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PShiftSumRule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.ShiftSumRule
namespace GroundTheory.Heights₂.Heights.RestTerms.ShiftSumRule
theorem _root_.solution (r a m : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        (X ((0 : Fin 1), i) : RootRing 1 (r + a)) ^ m =
      blockPowerSum 1 (r + a) m 0 - smallPowerSum 1 r a .last m 0 := by
  classical
  rw [eq_sub_iff_add_eq, blockPowerSum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin (r + a) => (i : ℕ) < a)]
  congr 1
  simp only [smallPowerSum, yRoot, SmallBlock.sign, map_one, one_mul, yIndex]
  refine Finset.sum_bij (fun j _ => (⟨a + (j : ℕ), by have := j.isLt; omega⟩ : Fin (r + a)))
    ?_ ?_ ?_ ?_
  · intro j _; simp
  · intro j₁ _ j₂ _ h
    simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at h
    exact Fin.ext h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact ⟨⟨(i : ℕ) - a, by have := i.isLt; omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
  · intro j _; rfl
end GroundTheory.Heights₂.Heights.RestTerms.ShiftSumRule

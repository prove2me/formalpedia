-- Prove2me | solution 1 for PI.WeylProdWork.weylProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:28:04.434965+00:00
-- url     : https://prove2.me/submissions/94c2b5ec-8ffa-45a0-b2f3-71c57ad5bd14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylProduct_WeylProd
import Theorems.Thm_PI_WeylProdWork_denom_eq
import Theorems.Thm_PI_WeylProdWork_row_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WeylProdWork
open Finset
namespace PI.WeylProdWork
theorem _root_.solution : PI.WeylProd := by
  intro n μ w c hμ
  have hterm : ∀ i j : Fin n,
      (((if i < j then (((μ i : ℤ) : ℚ) - ((μ j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1 : ℚ)) : ℝ) = wg (shiftSeq w) i j := by
    intro i j
    unfold wg
    by_cases h : i < j
    · have h' : (i : ℕ) < (j : ℕ) := h
      rw [if_pos h, if_pos h']
      have hi : shiftSeq w (i : ℕ) = ((w i : ℤ) : ℝ) - ((i : ℕ) : ℝ) := by
        simp [shiftSeq]
      have hj : shiftSeq w (j : ℕ) = ((w j : ℤ) : ℝ) - ((j : ℕ) : ℝ) := by
        simp [shiftSeq]
      rw [hi, hj, hμ i, hμ j]
      push_cast
      ring
    · have h' : ¬ (i : ℕ) < (j : ℕ) := h
      rw [if_neg h, if_neg h', Rat.cast_one]
  rw [Rat.cast_prod]
  simp only [Rat.cast_prod]
  rw [Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => hterm i j))]
  have e1 : ∀ i : ℕ, ∏ j : Fin n, wg (shiftSeq w) i (j : ℕ) = ∏ j ∈ range n, wg (shiftSeq w) i j :=
    fun i => Fin.prod_univ_eq_prod_range (wg (shiftSeq w) i) n
  simp only [e1]
  rw [Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ range n, wg (shiftSeq w) i j) n]
  simp only [row_eq]
  rw [Finset.prod_div_distrib, denom_eq]
  rfl
end PI.WeylProdWork

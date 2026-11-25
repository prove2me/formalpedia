-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CGlue.arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:12.978787+00:00
-- url     : https://prove2.me/submissions/83f62ce5-ea45-4825-be8a-11e25c7e050a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal
import Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_sum_fin_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CGlue
namespace PositivityTheory.Rg.Cz.CGlue
theorem _root_.solution (n : ℕ) (s : ℤ) (ν : Fin n → ℕ) (l : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (h : ∀ i, s - l (w i) = (ν i : ℤ) + (i : ℕ)) :
    (∑ i, (ν i : ℝ) * ((ν i : ℝ) + 2 * (i : ℕ) + 1 - n)) - (2 * s * ∑ i, (ν i : ℝ) - n * (s : ℝ) ^ 2) =
      ∑ k, (((l k : ℝ) + ((n : ℝ) - 1) / 2) ^ 2 - (((n : ℝ) - 1) / 2 - (k : ℕ)) ^ 2) := by
  have hl : ∀ i, (l (w i) : ℝ) = s - ν i - (i : ℕ) := by
    intro i
    have := congrArg (Int.cast : ℤ → ℝ) (h i)
    push_cast at this
    linarith
  have hm := sum_fin_val n
  rw [Finset.sum_sub_distrib, ← Equiv.sum_comp w (fun k => ((l k : ℝ) + ((n : ℝ) - 1) / 2) ^ 2),
    ← Finset.sum_sub_distrib]
  simp only [hl]
  have e : ∀ i : Fin n, ((s : ℝ) - ν i - (i : ℕ) + ((n : ℝ) - 1) / 2) ^ 2 - (((n : ℝ) - 1) / 2 - (i : ℕ)) ^ 2 =
      (ν i : ℝ) * ((ν i : ℝ) + 2 * (i : ℕ) + 1 - n) - 2 * s * ν i + (s : ℝ) ^ 2 + s * (n - 1) - 2 * s * (i : ℕ) := by
    intro i; ring
  rw [Finset.sum_congr rfl fun i _ => e i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  linear_combination (s : ℝ) * hm
end PositivityTheory.Rg.Cz.CGlue

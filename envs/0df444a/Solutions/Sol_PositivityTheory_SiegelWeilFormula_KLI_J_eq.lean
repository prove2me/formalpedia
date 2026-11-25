-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.J_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:20.571681+00:00
-- url     : https://prove2.me/submissions/a7953eaa-a094-4d10-b0a8-7753ff04fc64

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_ibp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution {b : ℂ} (hb : b.re < 0) : ∀ k c, J b k c = (pk b k).eval c * J b 0 c := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have h2b : (2 * b) ≠ 0 := mul_ne_zero two_ne_zero hb0
  have two : ∀ k, (∀ c, J b k c = (pk b k).eval c * J b 0 c) ∧ (∀ c, J b (k + 1) c = (pk b (k + 1)).eval c * J b 0 c) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun c => by simp [pk], fun c => ?_⟩
      have := J_ibp hb 0 c
      simp only [CharP.cast_eq_zero, zero_mul, neg_zero] at this
      simp only [pk, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      field_simp
      linear_combination this
    | succ k ih =>
      refine ⟨ih.2, fun c => ?_⟩
      have := J_ibp hb (k + 1) c
      simp only [Nat.add_sub_cancel] at this
      rw [ih.2 c, ih.1 c] at this
      simp only [pk, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add]
      field_simp
      push_cast at this ⊢
      linear_combination this
  exact fun k => (two k).1
end PositivityTheory.SiegelWeilFormula.KLI

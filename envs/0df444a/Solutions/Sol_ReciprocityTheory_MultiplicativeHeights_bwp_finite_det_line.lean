-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_finite_det_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:04.644486+00:00
-- url     : https://prove2.me/submissions/a625f30c-63bb-4bea-8525-673bae9887df

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_det_line_poly
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_finite_eval_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {p : ℕ} (z v : Fin p × Fin p → ℂ) (hz : (bwpMat z).det ≠ 0) :
    {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite := by
  obtain ⟨Λ, hΛ⟩ := bwp_det_line_poly z v
  have hΛ0 : Λ ≠ 0 := by
    intro h
    apply hz
    have h0 := hΛ 0
    rw [h, Polynomial.eval_zero] at h0
    simpa using h0.symm
  refine (bwp_finite_eval_eq_zero hΛ0).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [hΛ]
  exact ht
end ReciprocityTheory.MultiplicativeHeights

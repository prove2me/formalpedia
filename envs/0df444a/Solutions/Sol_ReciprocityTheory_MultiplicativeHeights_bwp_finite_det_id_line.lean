-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_finite_det_id_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:19.722684+00:00
-- url     : https://prove2.me/submissions/6898222f-141e-45f4-969d-1f0eabea9f3a

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyC
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
theorem _root_.solution {p : ℕ} (z : Fin p × Fin p → ℂ) :
    {s : ℂ | (bwpMat (z + s • bwpId p)).det = 0}.Finite := by
  have hne : (-bwpMat z).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  refine (bwp_finite_eval_eq_zero hne).subset fun s hs => ?_
  simp only [Set.mem_setOf_eq] at hs ⊢
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  convert hs using 2
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply]
    ring
  · simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply, h]
end ReciprocityTheory.MultiplicativeHeights

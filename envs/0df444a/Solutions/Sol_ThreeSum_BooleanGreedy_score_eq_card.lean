-- Prove2me | solution 1 for ThreeSum.BooleanGreedy.score_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:46:27.003194+00:00
-- url     : https://prove2.me/submissions/4a338f51-2bd3-4970-bcc8-67378caea88a

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Theorems.Thm_ThreeSum_BooleanGreedy_state_subset
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.BooleanGreedy
open Finset
open scoped BigOperators
namespace ThreeSum.BooleanGreedy
theorem _root_.solution {matrix : ℕ → ℕ → ℕ} {rows cols row : ℕ}
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hrow : row < rows) (t : ℕ) :
    LightCoverScores.score matrix (active matrix rows cols t) cols row =
      ((state matrix rows cols t).filter (covers matrix row)).card := by
  have hset : ((range cols).filter fun j => j ∈ state matrix rows cols t ∧ covers matrix row j) =
      (state matrix rows cols t).filter (covers matrix row) := by
    ext j
    simp only [mem_filter]
    constructor
    · rintro ⟨_,hmem,hcover⟩
      exact ⟨hmem,hcover⟩
    · rintro ⟨hmem,hcover⟩
      exact ⟨state_subset matrix rows cols t hmem,hmem,hcover⟩
  rw [← hset,Finset.card_filter]
  unfold LightCoverScores.score LightBooleanDot.dot
  apply sum_congr rfl
  intro j hj
  have hm := hmatrix row hrow j (mem_range.mp hj)
  by_cases ha : j ∈ state matrix rows cols t <;> by_cases hc : matrix row j = 1
  · simp [active,ha,covers,hc]
  · have hz : matrix row j = 0 := by omega
    simp [active,ha,covers,hc,hz]
  · simp [active,ha,covers,hc]
  · simp [active,ha,covers,hc]
end ThreeSum.BooleanGreedy

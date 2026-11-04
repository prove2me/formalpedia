-- Prove2me | solution 1 for ThreeSum.BooleanGreedy.active_succ_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:32.027542+00:00
-- url     : https://prove2.me/submissions/56c3c9e5-2645-4b00-884a-6716149bf956

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Theorems.Thm_ThreeSum_BooleanGreedy_choice_lt
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
theorem _root_.solution {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ}
    (hrows : 0 < rows)
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1) (t j : ℕ) (hj : j < cols) :
    active matrix rows cols (t+1) j =
      active matrix rows cols t j * (1-matrix (choice matrix rows cols t) j) := by
  have hm := hmatrix _ (choice_lt (matrix := matrix) (cols := cols) hrows t) j hj
  have hmem : j ∈ state matrix rows cols (t+1) ↔
      j ∈ state matrix rows cols t ∧ ¬covers matrix (choice matrix rows cols t) j :=
    Finset.mem_filter
  by_cases ha : j ∈ state matrix rows cols t <;>
    by_cases hc : matrix (choice matrix rows cols t) j = 1
  · have hn : j ∉ state matrix rows cols (t+1) := fun h => (hmem.mp h).2 hc
    simp only [active,if_neg hn,if_pos ha,hc,Nat.sub_self,Nat.mul_zero]
  · have hz : matrix (choice matrix rows cols t) j = 0 := by omega
    have hn : j ∈ state matrix rows cols (t+1) := hmem.mpr ⟨ha,hc⟩
    simp only [active,if_pos hn,if_pos ha,hz,Nat.sub_zero,Nat.mul_one]
  · have hn : j ∉ state matrix rows cols (t+1) := fun h => ha (hmem.mp h).1
    simp only [active,if_neg hn,if_neg ha,Nat.zero_mul]
  · have hn : j ∉ state matrix rows cols (t+1) := fun h => ha (hmem.mp h).1
    simp only [active,if_neg hn,if_neg ha,Nat.zero_mul]
end ThreeSum.BooleanGreedy

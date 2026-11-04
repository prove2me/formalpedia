-- Prove2me | solution 1 for ThreeSum.BooleanGreedy.choice_eq_least_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:34.069023+00:00
-- url     : https://prove2.me/submissions/1e4a60db-bc1c-41d2-b754-2304d74ea61b

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Theorems.Thm_ThreeSum_BooleanGreedy_score_eq_card
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_IndexedGreedy_selectMap_indices
import Theorems.Thm_ThreeSum_LightMinimum_least_lt
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
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1) (t : ℕ) :
    choice matrix rows cols t =
      LightMinimum.least (fun i => -(LightCoverScores.score matrix (active matrix rows cols t) cols i : ℤ)) rows := by
  have hf : ∀ i < rows,
      -(((state matrix rows cols t).filter (covers matrix i)).card : ℤ) =
      -(LightCoverScores.score matrix (active matrix rows cols t) cols i : ℤ) := by
    intro i hi
    rw [score_eq_card hmatrix hi t]
  rw [choice,IndexedGreedy.selectMap_indices _ _ hrows]
  have hcongr (f g : ℕ → ℤ) : ∀ n, (∀ i < n, f i = g i) →
      LightMinimum.least f n = LightMinimum.least g n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro he
      cases n with
      | zero => simp [LightMinimum.least]
      | succ n =>
        have hb := LightMinimum.least_lt g (by omega : 0 < n+1)
        have hi := ih (fun i hi => he i (by omega))
        change (if f (n+1) < f (LightMinimum.least f (n+1)) then n+1 else _) = _
        rw [hi,he (n+1) (by omega),he _ (by omega)]
        rfl
  exact hcongr _ _ rows hf
end ThreeSum.BooleanGreedy

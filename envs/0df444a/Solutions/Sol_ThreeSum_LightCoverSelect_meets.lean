-- Prove2me | solution 1 for ThreeSum.LightCoverSelect.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:57.784254+00:00
-- url     : https://prove2.me/submissions/dca056c2-f8ef-44aa-92e9-51c0c1ecfb8a

import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverSelect
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverSelect
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCoverSelect
theorem _root_.solution {pMain pScores pDot pMinimum : ℕ} (hmain : P[pMain]? = some (body pScores pMinimum))
    (hscores : P[pScores]? = some (LightCoverScores.body pDot)) (hdot : P[pDot]? = some LightBooleanDot.body)
    (hminimum : P[pMinimum]? = some LightMinimum.body) {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) (hrows : 0 < rows)
    (hsrc : src + rows * cols ≤ work) (hactive : activePtr + cols ≤ work) (hspace : work + rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src + i * cols + j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr + j) = (active j : ℤ)) (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1) (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src, activePtr, work, rows, cols] μ (time rows cols)
      (fun r μ' =>
        r = (LightMinimum.least (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
          SameOutside μ μ' work rows) :=
  by
  apply Meets.of_body hmain
  unfold body time
  have hc :=
    LightCoverScores.meets (d := d + 1) (μ := μ) (src := src) (activePtr := activePtr) (dst := work) (rows := rows)
      (cols := cols) hscores hdot matrix active hw hd hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightCoverScores.time, LightBooleanDot.time,
            LightMinimum.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightCoverScores.time, LightBooleanDot.time, LightMinimum.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightCoverScores.time, LightBooleanDot.time,
            LightMinimum.time] <;>
          omega)
    on_goal -1 => (rintro v μ₁ ⟨written, kept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hm :=
    LightMinimum.meets (d := d + 1) (μ := μ₁) (src := work) (n := rows) hminimum
      (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) hw hrows hspace written
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hm _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hm ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightCoverScores.time, LightBooleanDot.time,
            LightMinimum.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightCoverScores.time, LightBooleanDot.time, LightMinimum.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightCoverScores.time, LightBooleanDot.time,
            LightMinimum.time] <;>
          omega)
    on_goal -1 => (rintro r μ₂ ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  exact ⟨hr, kept⟩
end ThreeSum.LightCoverSelect

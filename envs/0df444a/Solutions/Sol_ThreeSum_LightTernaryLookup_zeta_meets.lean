-- Prove2me | solution 1 for ThreeSum.LightTernaryLookup.zeta_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:25.127915+00:00
-- url     : https://prove2.me/submissions/b1a28f12-e302-446a-b1ff-a5518b5df010

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Theorems.Thm_ThreeSum_LightTernaryLookup_code_meets
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_LightTernaryCell_zeta_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryLookup
theorem _root_.solution {pMain pSearch pCell a n powers W L src j0 j1 j2 d U : ℕ}
    (hmain : P[pMain]? = some (body pSearch pCell)) (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hcell : P[pCell]? = some LightTernaryCell.zetaBody) (μ : ℕ → ℤ) (codes : ℕ → ℤ) (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ lim.space) (hsrc : src + n ≤ lim.space)
    (hspace : powers + (W + 1) ≤ lim.space) (hword : ((n + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a + i) = codes i) (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k) (hj0 : j0 < n) (hj1 : j1 < n) (hj2 : j2 < n)
    (hr0 : μ (src + j0) = f 0) (hr1 : μ (src + j1) = f 1) (hr2 : μ (src + j2) = f 2) (hf : ∀ e, |f e| ≤ U)
    (hvalue : 4 * (U : ℤ) + 3 ≤ lim.word) (hL : L ≤ W) (hn : n < 2 ^ L) (hd : d + L + 1 ≤ lim.depth) :
    Meets lim P pMain d [a, n, powers, L, q.val, codes j0, codes j1, codes j2, src] μ (time L)
      (fun r μ' => r = ThreeSum.TernaryQuery.zetaDigit f q ∧ μ' = μ) :=
  by
  have hc0 := code_meets hsearch μ codes hw ha hspace hword hread hpowers hsorted hj0 hL hn (d := d + 1) (by omega)
  have hc1 := code_meets hsearch μ codes hw ha hspace hword hread hpowers hsorted hj1 hL hn (d := d + 1) (by omega)
  have hc2 := code_meets hsearch μ codes hw ha hspace hword hread hpowers hsorted hj2 hL hn (d := d + 1) (by omega)
  have hc :=
    LightTernaryCell.zeta_meets (d := d + 1) hcell q f hw (a0 := src + j0) (a1 := src + j1) (a2 := src + j2) (by omega)
      (by omega) (by omega) hr0 hr1 hr2 hf hvalue
  have ha0 : (src : ℤ) + ((j0 + 1 : ℕ) : ℤ) - 1 = ((src + j0 : ℕ) : ℤ) := by omega
  have ha1 : (src : ℤ) + ((j1 + 1 : ℕ) : ℤ) - 1 = ((src + j1 : ℕ) : ℤ) := by omega
  have ha2 : (src : ℤ) + ((j2 + 1 : ℕ) : ℤ) - 1 = ((src + j2 : ℕ) : ℤ) := by omega
  apply Meets.of_body hmain
  unfold body time
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
    | refine _root_.Light.Ends.callToThen (hc0 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc0 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBandLookup.searchTime,
            LightTernaryCell.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBandLookup.searchTime, LightTernaryCell.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandLookup.searchTime,
            LightTernaryCell.time] <;>
          omega)
    on_goal -1 => (rintro r0 μ0 ⟨h0, hm0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ0
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
    | refine _root_.Light.Ends.callToThen (hc1 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc1 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBandLookup.searchTime,
            LightTernaryCell.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBandLookup.searchTime, LightTernaryCell.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandLookup.searchTime,
            LightTernaryCell.time] <;>
          omega)
    on_goal -1 => (rintro r1 μ1 ⟨h1, hm1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ1
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
    | refine _root_.Light.Ends.callToThen (hc2 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc2 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBandLookup.searchTime,
            LightTernaryCell.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBandLookup.searchTime, LightTernaryCell.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandLookup.searchTime,
            LightTernaryCell.time] <;>
          omega)
    on_goal -1 => (rintro r2 μ2 ⟨h2, hm2⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ2
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, h0, h1, h2, ha0, ha1, ha2,
            LightBandLookup.searchTime, LightTernaryCell.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [h0, h1, h2, ha0, ha1, ha2, LightBandLookup.searchTime, LightTernaryCell.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, h0, h1, h2, ha0, ha1, ha2,
            LightBandLookup.searchTime, LightTernaryCell.time] <;>
          omega)
    on_goal -1 => (rintro r μ' ⟨hr, hm⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  exact ⟨hr, hm⟩
end ThreeSum.LightTernaryLookup

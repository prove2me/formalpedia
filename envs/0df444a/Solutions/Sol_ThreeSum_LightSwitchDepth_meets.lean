-- Prove2me | solution 1 for ThreeSum.LightSwitchDepth.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:45.380428+00:00
-- url     : https://prove2.me/submissions/cc56b2a9-827e-41de-9e14-b0004bfb517d

import Definitions.Def_Submission_ThreeSum_LightSwitch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSwitch_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchDepth
open Light
variable {lim : Limits} {P : Program} {μ : ℕ → ℤ} {J d : ℕ}
namespace ThreeSum.LightSwitchDepth
theorem _root_.solution {p pDiv : ℕ} (hp : P[p]? = some (body pDiv)) (hdiv : P[pDiv]? = some LightSmallDivide.body)
    (hword : (word J : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P p d [J] μ (time J) (fun result ν => result = (depth J : ℤ) ∧ ν = μ) :=
  by
  unfold word at hword
  apply Meets.of_body hp
  unfold body time
  have hc := LightSmallDivide.meets (d := d + 1) (a := 13 * J) (b := 20) hdiv μ hword
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, word, LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [word, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, word, LightSmallDivide.time] <;> omega)
    on_goal -1 => (rintro result ν ⟨hresult, rfl⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (depth J) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, depth, word, LightSmallDivide.time, hresult]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [depth, word, LightSmallDivide.time, hresult] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, depth, word, LightSmallDivide.time, hresult] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, rfl⟩
end ThreeSum.LightSwitchDepth

-- Prove2me | solution 1 for ThreeSum.LightTernaryCodes.zero_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:41:29.854135+00:00
-- url     : https://prove2.me/submissions/da11278c-d6b3-424a-a70b-ce8dd916951d

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_88b09a412b2c33a9
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCodes
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryCodes
theorem _root_.solution {pMain pErase W low high m powers d : ℕ} (hmain : P[pMain]? = some (zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers + (W + 1) ≤ lim.space) (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (hpowers : Powers μ powers W)
    (hlow : low ≤ W) (hhigh : high ≤ W) (hm : m < 2 ^ W) (hd : d + W + 1 ≤ lim.depth) :
    Meets lim P pMain d [W, low, high, m, powers] μ (zeroTime W)
      (fun r μ' => r = (zeroCode W low high m : ℤ) ∧ μ' = μ) :=
  by
  have hupper := LightMaskErase.meets herase μ hw hspace hword hpowers W high m le_rfl hhigh hm (d + 1) (by omega)
  have hu : eraseMask W high m < 2 ^ W := (eraseMask_le hm).trans_lt hm
  have hlower :=
    LightMaskErase.meets herase μ hw hspace hword hpowers W low (eraseMask W high m) le_rfl hlow hu (d + 1) (by omega)
  apply Meets.of_body hmain
  unfold zeroBody zeroTime
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
    | refine _root_.Light.Ends.callToThen (hupper _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hupper ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskErase.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskErase.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskErase.time] <;> omega)
    on_goal -1 => (rintro r1 μ1 ⟨hr1, hm1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
    | refine _root_.Light.Ends.callToThen (hlower _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hlower ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr1, LightMaskErase.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hr1, LightMaskErase.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr1, LightMaskErase.time] <;> omega)
    on_goal -1 => (rintro r μ' ⟨hr, hm'⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  exact ⟨hr, hm'⟩
end ThreeSum.LightTernaryCodes

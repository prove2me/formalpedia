-- Prove2me | solution 1 for ThreeSum.LightHeaderBands.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:12.317549+00:00
-- url     : https://prove2.me/submissions/c366eda0-3909-4c1c-b876-69ed03d680df

import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
set_option autoImplicit false
open ThreeSum ThreeSum.LightHeaderBands
open Light ThreeSum.BandEnumeration
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightHeaderBands
namespace Procs
theorem _root_.solution {pMain a b c nA nB nC dst U d : ℕ} {μ : ℕ → ℤ} (R : Procs P pMain) (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + 2 + nA + A.size ≤ dst) (hb : b + 2 + nB + B.size ≤ dst)
    (hc : c + 2 + nC + C.size ≤ dst) (hspace : LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d + LightBandEnumeration.width A.size B.size C.size + 5 ≤ lim.depth) (hA : At μ a nA A) (hB : At μ b nB B)
    (hC : At μ c nC C) (hAU : LightBandEnumeration.Bounded A U) (hBU : LightBandEnumeration.Bounded B U)
    (hCU : LightBandEnumeration.Bounded C U) :
    Meets lim P pMain d [a, b, c, dst] μ (time A.size B.size C.size)
      (fun r μ' =>
        r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
          LightBandEnumeration.Tables μ' dst A B C ∧ Kept μ μ' dst) :=
  by
  obtain ⟨han, has, hA⟩ := hA
  obtain ⟨hbn, hbs, hB⟩ := hB
  obtain ⟨hcn, hcs, hC⟩ := hC
  have hspace' :
    dst + LightBandEnumeration.count A.size B.size C.size + LightBandEnumeration.width A.size B.size C.size + 1 ≤
      lim.space :=
    hspace
  apply Meets.of_body R.main
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((R.enumerate.meets (d := d + 1) A B C hw (by omega) ha (by omega) hb (by omega) hc hspace hword (by omega) hA
              hB hC hAU hBU hCU)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (R.enumerate.meets (d := d + 1) A B C hw (by omega) ha (by omega) hb (by omega) hc hspace hword (by omega) hA
            hB hC hAU hBU hCU)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, han, has, hbn, hbs, hcn, hcs,
            LightBandEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [han, has, hbn, hbs, hcn, hcs, LightBandEnumeration.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, han, has, hbn, hbs, hcn, hcs,
            LightBandEnumeration.time] <;> omega)
    on_goal -1 => (rintro result μ' hresult; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  exact hresult
end Procs
end ThreeSum.LightHeaderBands

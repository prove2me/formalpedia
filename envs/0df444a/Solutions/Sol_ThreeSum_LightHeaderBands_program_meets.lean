-- Prove2me | solution 1 for ThreeSum.LightHeaderBands.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:33.992677+00:00
-- url     : https://prove2.me/submissions/24eb843c-6861-45ca-a16c-61b0aa54f841

import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs
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
theorem _root_.solution {a b c nA nB nC dst U d : ℕ} {μ : ℕ → ℤ}
    (A B C : Family) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+2+nA+A.size ≤ dst) (hb : b+2+nB+B.size ≤ dst)
    (hc : c+2+nC+C.size ≤ dst)
    (hspace : LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+LightBandEnumeration.width A.size B.size C.size+5 ≤ lim.depth)
    (hA : At μ a nA A) (hB : At μ b nB B) (hC : At μ c nC C)
    (hAU : LightBandEnumeration.Bounded A U) (hBU : LightBandEnumeration.Bounded B U)
    (hCU : LightBandEnumeration.Bounded C U) :
    Meets lim program 0 d [a,b,c,dst] μ (time A.size B.size C.size)
      (fun r μ' => r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        LightBandEnumeration.Tables μ' dst A B C ∧ Kept μ μ' dst) :=
  program_procs.meets A B C hw ha hb hc hspace hword hd hA hB hC hAU hBU hCU
end ThreeSum.LightHeaderBands

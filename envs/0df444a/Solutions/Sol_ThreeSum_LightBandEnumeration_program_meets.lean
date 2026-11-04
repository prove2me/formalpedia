-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:09.058854+00:00
-- url     : https://prove2.me/submissions/7c0754f6-0869-48a8-bfec-e41c6bbada72

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandEnumeration
theorem _root_.solution {al ah bl bh cl ch dst U d : ℕ} {μ : ℕ → ℤ}
    (A B C : Family) (hw : (lim.space : ℤ) ≤ lim.word)
    (hal : al+A.size ≤ dst) (hah : ah+A.size ≤ dst)
    (hbl : bl+B.size ≤ dst) (hbh : bh+B.size ≤ dst)
    (hcl : cl+C.size ≤ dst) (hch : ch+C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space)
    (hword : (word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+width A.size B.size C.size+4 ≤ lim.depth)
    (hA : At μ al ah A) (hB : At μ bl bh B) (hC : At μ cl ch C)
    (hAU : Bounded A U) (hBU : Bounded B U) (hCU : Bounded C U) :
    Meets lim program 0 d [al,ah,bl,bh,cl,ch,A.size,B.size,C.size,dst] μ
      (time A.size B.size C.size)
      (fun r μ' => r = (count A.size B.size C.size : ℤ) ∧
        Tables μ' dst A B C ∧ Kept μ μ' dst) :=
  program_procs.meets A B C hw hal hah hbl hbh hcl hch hspace hword hd hA hB hC hAU hBU hCU
end ThreeSum.LightBandEnumeration

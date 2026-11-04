-- Prove2me | solution 1 for ThreeSum.LightSortedBands.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:23.967357+00:00
-- url     : https://prove2.me/submissions/561bde25-8d21-4bb8-b864-0e320b453fb8

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab


set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSortedBands
theorem _root_.solution {src values endpoints work g d : ℕ}
    {μ : ℕ → ℤ} {original : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+original.length ≤ values) (hvalues : values+original.length ≤ endpoints)
    (hendpoints : endpoints+2+2*original.length ≤ work)
    (hspace : space work original.length ≤ lim.space)
    (hword : ((original.length+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+original.length+Nat.clog 2 original.length+3 ≤ lim.depth)
    (hread : Seg μ src original) :
    Meets lim program 0 d [src,original.length,g,values,endpoints,work] μ (time original.length)
      (fun r μ' => r = μ' (endpoints+1) ∧ Prepared μ' values endpoints g original ∧
        ∀ a, a < work → (a < src ∨ src+original.length ≤ a) →
          (a < values ∨ values+original.length ≤ a) →
          (a < endpoints ∨ endpoints+2+2*original.length ≤ a) → μ' a = μ a) :=
  program_procs.meets hw hg hsrc hvalues hendpoints hspace hword hd hread
end ThreeSum.LightSortedBands

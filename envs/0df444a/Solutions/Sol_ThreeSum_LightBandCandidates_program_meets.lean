-- Prove2me | solution 1 for ThreeSum.LightBandCandidates.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:35:13.315866+00:00
-- url     : https://prove2.me/submissions/3ba712ce-65e2-4ecb-9941-f4dd482883ef

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
import Definitions.Def_Submission_ThreeSum_LightBandCandidates
import Definitions.Def_WeightedCache3SUM_Alias_f945b0797ad8c830
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_887023f6a62327ec
import Definitions.Def_WeightedCache3SUM_Alias_66a9a0be433f5f2b
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandCandidates
open Light BandEnumeration BandCandidateRows
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src dst : ℕ}
namespace ThreeSum.LightBandCandidates
theorem _root_.solution (A B C : Family) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth)
    (hsrc : src + LightBandEnumeration.count A.size B.size C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space) (hword : (word A.size B.size C.size : ℤ) ≤ lim.word)
    (htables : LightBandEnumeration.Tables μ src A B C) :
    Meets lim program 0 d [src, dst, A.size, B.size, C.size] μ (time A.size B.size C.size)
      (fun r ν =>
        r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
          Seg ν dst (cells (records A B C)) ∧
            SameOutside μ ν dst (4 * LightBandEnumeration.count A.size B.size C.size)) :=
  programProcs.meets A B C hw hd hsrc hspace hword htables
end ThreeSum.LightBandCandidates

-- Prove2me | solution 1 for ThreeSum.LightBandRawA.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:23:37.656806+00:00
-- url     : https://prove2.me/submissions/866d2a45-1d97-4159-a219-48f5afa062ba

import Definitions.Def_Submission_ThreeSum_LightBandRawAStep
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Definitions.Def_WeightedCache3SUM_Alias_0eeb60918c21319a
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3284ee33b9feff11
import Definitions.Def_WeightedCache3SUM_Alias_09621c124e09fb6e
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
open ThreeSum ThreeSum.LightBandRawA
open Light BandCandidateRows BandRawA
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}
namespace ThreeSum.LightBandRawA
theorem _root_.solution (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) (hg : 0 < g)
    (hrecords : records + 4 * rs.length ≤ vals) (hsrc : src + n ≤ vals) (hspace : space vals rs.length g ≤ lim.space)
    (hword : (word n g rs.length : ℤ) ≤ lim.word)
    (hvalid : ∀ i < rs.length, (rs.getD i default).flag = 1 → (rs.getD i default).a < BandPartition.size n g)
    (hrecordRead : Seg μ records (cells rs)) (hread : ∀ j < n, μ (src + j) = f j) :
    Meets lim program 0 d [records, rs.length, src, n, g, vals] μ (time rs.length g)
      (fun r ν =>
        r = ((items n g rs).length : ℤ) ∧
          Stored ν vals (ownerBase vals rs.length g) (positionBase vals rs.length g) f (items n g rs) ∧
            Kept μ ν vals) :=
  programProcs.meets hw hd hg hrecords hsrc hspace hword hvalid hrecordRead hread
end ThreeSum.LightBandRawA

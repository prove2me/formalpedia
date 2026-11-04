-- Prove2me | solution 1 for ThreeSum.LightWantedJoin.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:19:42.510203+00:00
-- url     : https://prove2.me/submissions/ce9973a5-e55f-4c42-893b-5d8534c42691

import Definitions.Def_Submission_ThreeSum_LightWantedRow
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedJoin
open Light SourceBuckets WantedPairs
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWantedJoin
theorem _root_.solution {keys offsets flat NR M dst n d : ℕ} {μ : ℕ → ℤ} (left right : ℕ → ℕ)
    (hright : ∀ j < NR, right j < M) (hw : (lim.space : ℤ) ≤ lim.word) (hkeys : keys + n ≤ dst)
    (hoffsets : offsets + M + 1 ≤ dst) (hflat : flat + NR ≤ dst) (hspace : dst + 2 * count left right NR n ≤ lim.space)
    (hd : d + n + 2 ≤ lim.depth) (hleft : ∀ i < n, left i < M) (hread : ∀ i < n, μ (keys + i) = (left i : ℤ))
    (H : Stored μ right NR M offsets flat) :
    Meets lim program 0 d [keys, offsets, flat, n, NR, M, dst] μ (time left right NR n)
      (fun r ν => r = (count left right NR n : ℤ) ∧ Seg ν dst (cells (pairs μ offsets flat left n)) ∧ Kept μ ν dst) :=
  meets rfl rfl left right hright n d μ hw hkeys hoffsets hflat hspace hd hleft hread H
end ThreeSum.LightWantedJoin

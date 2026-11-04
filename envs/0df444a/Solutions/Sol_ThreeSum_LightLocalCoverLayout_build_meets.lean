-- Prove2me | solution 1 for ThreeSum.LightLocalCoverLayout.build_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:42:11.775248+00:00
-- url     : https://prove2.me/submissions/7eb0b805-d1ae-4951-9ba3-8f5acec444d3

import Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_2311045817689c86
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_942628883105a84f
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_ed969675cd1be1e3
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_a495b72bdff1a7b5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverLayout
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
namespace ThreeSum.LightLocalCoverLayout
theorem _root_.solution {lim : Limits} {P : Program} {d pMain : ℕ}
    (S : LightLocalCoverBuild.Procs P pMain) {μ : ℕ → ℤ} {base h : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+7 ≤ lim.depth)
    (hspace : space base h ≤ lim.space) (hword : (LightLocalCoverBuild.word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d
      [512*h,h,localPrime h,rows h,vertices h,localBucketCap h,base,bitPtr base h,maps base h,
        raw0 base h,raw1 base h,hist0 base h,hist1 base h,matrixPtr base h,work base h,
        scheduleSize h,scheduleMaps base h]
      μ (LightLocalCoverBuild.time h)
      (fun r ν => r = (scheduleMaps base h : ℤ) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν base) := by
  exact S.meets hw hd ((Nat.le_max_left ..).trans hspace) le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl ((Nat.le_max_right ..).trans hspace) hword
end ThreeSum.LightLocalCoverLayout

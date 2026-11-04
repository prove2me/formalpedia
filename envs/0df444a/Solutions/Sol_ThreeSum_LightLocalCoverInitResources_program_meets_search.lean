-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.program_meets_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:08:48.221203+00:00
-- url     : https://prove2.me/submissions/a9f083a1-f54e-4638-9bb0-e98cb60e28c2

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_meets_search
import Theorems.Thm_ThreeSum_LightLocalCoverResources_meets_search


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution {lim : Limits} {d n free : ℕ} {μ : ℕ → ℤ}
    (hh : 1 ≤ Scales.microHalf (Scales.inputBits n))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+Scales.localSearch 5000000 n ≤ lim.depth)
    (hspace : free+Scales.localSearch 5000000 n ≤ lim.space)
    (hword : (Scales.localSearch 5000000 n : ℤ) ≤ lim.word) :
    let h := Scales.microHalf (Scales.inputBits n)
    let base := LightLocalCoverInit.base free
    Meets lim LightLocalCoverInit.program 52 d [h,free] μ (Scales.localSearch 5000000 n)
      (fun r ν => r = (LightLocalCoverMetadata.nextFree base h : ℤ) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν free) :=
  meets_search LightLocalCoverInit.programProcs hh hw hd hspace hword
end ThreeSum.LightLocalCoverInitResources

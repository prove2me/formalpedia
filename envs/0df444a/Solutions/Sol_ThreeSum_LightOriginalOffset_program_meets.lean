-- Prove2me | solution 1 for ThreeSum.LightOriginalOffset.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:30.117229+00:00
-- url     : https://prove2.me/submissions/c7ae2e04-14fb-47ef-a673-6cde2f6e9cfc

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e


set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightOriginalOffset
theorem _root_.solution {a b nLeft nRight p N free U : ℕ} [NeZero p] {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nLeft ≤ free) (hb : b+nRight ≤ free)
    (hnLeft : nLeft ≤ N) (hnRight : nRight ≤ N)
    (hspace : space free p N U ≤ lim.space) (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 p+4 ≤ lim.depth)
    (hLeft : ∀ i < nLeft, |μ (a+i)| ≤ (U : ℤ))
    (hRight : ∀ i < nRight, |μ (b+i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [a,b,nLeft,nRight,p,N,free] μ (time p nLeft nRight U)
      (fun r ν => r = (selected p (fun i => μ (a+i)) (fun i => μ (b+i)) nLeft nRight : ℤ) ∧
        Kept μ ν free) :=
  programProcs.meets hw ha hb hnLeft hnRight hspace hword hd hLeft hRight
end ThreeSum.LightOriginalOffset

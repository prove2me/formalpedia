-- Prove2me | solution 1 for ThreeSum.LightSelectedPrime.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:22.219015+00:00
-- url     : https://prove2.me/submissions/84cdb0b9-804d-4408-9cd1-4bbd060639b9

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e


set_option autoImplicit false
open ThreeSum ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSelectedPrime
theorem _root_.solution {μ : ℕ → ℤ} {N free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hN : 0 < N) (hspace : space free N ≤ lim.space)
    (hword : (word N : ℤ) ≤ lim.word) :
    Meets lim program 0 d [N,free] μ (time N)
      (fun r μ' => r = (selectedPrime N : ℤ) ∧
        SegN μ' free (LightPrimePool.values (rootCeiling N)) ∧ Kept μ μ' free) :=
  procs.meets hw hd hN hspace hword
end ThreeSum.LightSelectedPrime

-- Prove2me | solution 1 for ThreeSum.LightPrimePool.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:31.790993+00:00
-- url     : https://prove2.me/submissions/688e38a3-ce56-4c9c-b332-29bb58f6dd85

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e


set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPrimePool
theorem _root_.solution
    {μ : ℕ → ℤ} {y free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hy : 0 < y) (hspace : space free y ≤ lim.space)
    (hword : (word y : ℤ) ≤ lim.word) :
    Meets lim program 0 d [y,free] μ (time y)
      (fun r μ' => r = (size y : ℤ) ∧ SegN μ' free (values y) ∧ Kept μ μ' free) :=
  program_procs.meets hw hd hy hspace hword
end ThreeSum.LightPrimePool

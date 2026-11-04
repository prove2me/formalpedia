-- Prove2me | solution 1 for ThreeSum.LightPrimality.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:06.505033+00:00
-- url     : https://prove2.me/submissions/ff77f57d-aa6f-4011-8db0-be64245dafd8

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
import Theorems.Thm_ThreeSum_LightPrimality_time_le_uniform
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono


set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPrimality
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {n free maxValue : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hn : 2 ≤ n) (hmax : n ≤ maxValue)
    (hspace : free+(Nat.log 2 (maxValue+1)+2) ≤ lim.space)
    (hword : (8*maxValue+16 : ℕ) ≤ lim.word) :
    Meets lim P pMain d [n,free] μ (time maxValue maxValue)
      (fun r μ' => r = (answer n : ℤ) ∧ Kept μ μ' free) := by
  exact (LightPrimality.meets S.main S.emod hw hd hn hmax hspace hword).mono
    (time_le_uniform hmax) (fun _ _ h => h)
end Procs
end ThreeSum.LightPrimality

-- Prove2me | solution 1 for ThreeSum.LightPrimality.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:55.783723+00:00
-- url     : https://prove2.me/submissions/6b8306ca-2845-4dcd-a96e-92545f88db83

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPrimality
theorem _root_.solution
    {μ : ℕ → ℤ} {n free maxValue : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hn : 2 ≤ n) (hmax : n ≤ maxValue)
    (hspace : free+(Nat.log 2 (maxValue+1)+2) ≤ lim.space)
    (hword : (8*maxValue+16 : ℕ) ≤ lim.word) :
    Meets lim program 0 d [n,free] μ (time maxValue maxValue)
      (fun r μ' => r = (answer n : ℤ) ∧ Kept μ μ' free) :=
  program_procs.meets hw hd hn hmax hspace hword
end ThreeSum.LightPrimality

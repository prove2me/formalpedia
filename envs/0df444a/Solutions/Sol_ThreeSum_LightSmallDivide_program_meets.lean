-- Prove2me | solution 1 for ThreeSum.LightSmallDivide.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:33.7592+00:00
-- url     : https://prove2.me/submissions/b288ca44-54f6-4d11-a4a0-dda312d3bbc2

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightSmallDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSmallDivide
theorem _root_.solution {a b : ℕ} (μ : ℕ → ℤ)
    (hword : ((a+b+2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [a,b] μ (time a b)
      (fun r μ' => r = ((a/b : ℕ) : ℤ) ∧ μ' = μ) :=
  meets rfl μ hword
end ThreeSum.LightSmallDivide

-- Prove2me | solution 1 for ThreeSum.LightCapacity.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:33.106472+00:00
-- url     : https://prove2.me/submissions/704234a1-0568-4c3d-a821-1641c85ed9f6

import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf


set_option autoImplicit false
open ThreeSum ThreeSum.LightCapacity
open Light ThreeSum.KaratsubaInterface
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCapacity
theorem _root_.solution {p : ℕ} (μ : ℕ → ℤ) (hp : 0 < p)
    (hword : ((2*p+1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [p] μ (time p)
      (fun r μ' => r = (capacity p : ℤ) ∧ μ' = μ) :=
  meets rfl μ hp hword
end ThreeSum.LightCapacity

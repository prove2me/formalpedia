-- Prove2me | solution 1 for ThreeSum.LightRadixDigit.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:54.214278+00:00
-- url     : https://prove2.me/submissions/ecf138fa-36fd-429c-97d8-47883aee61f1

import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab


set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixDigit
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightRadixDigit
theorem _root_.solution {k b p : ℕ} (μ : ℕ → ℤ)
    (hd : d < lim.depth) (hword : (word k b p : ℤ) ≤ lim.word) :
    Meets lim program 0 d [k,b,p] μ (time k)
      (fun r μ' => r = (((k/b)%p : ℕ) : ℤ) ∧ μ'=μ) :=
  meets rfl rfl μ hd hword
end ThreeSum.LightRadixDigit

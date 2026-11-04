-- Prove2me | solution 1 for ThreeSum.LightNatPower.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:07.251602+00:00
-- url     : https://prove2.me/submissions/094ff98d-3d1f-439c-93ef-29cecffa3749

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac

set_option autoImplicit false
open ThreeSum ThreeSum.LightNatPower
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightNatPower
theorem _root_.solution {b e : ℕ} (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hpow : ∀ i ≤ e, ((b^i : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [b,e] μ (time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) :=
  meets rfl μ he hpow
end ThreeSum.LightNatPower

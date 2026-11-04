-- Prove2me | solution 1 for ThreeSum.LightSign.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:05.399986+00:00
-- url     : https://prove2.me/submissions/3218196d-ee82-4360-8723-c2c56712452d

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightSign
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556

set_option autoImplicit false
open ThreeSum ThreeSum.LightSign
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSign
theorem _root_.solution {e d : ℕ} {x : ℤ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (he : e ≤ lim.space)
    (hvalue : |x| ≤ lim.word) :
    Meets lim program 0 d [x,e] μ (time e)
      (fun r μ' => r = (-1 : ℤ)^e*x ∧ μ' = μ) :=
  meets rfl hw he hvalue
end ThreeSum.LightSign

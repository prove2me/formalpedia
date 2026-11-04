-- Prove2me | solution 1 for ThreeSum.LightOutputDecodeDivide.bounded_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:18.851375+00:00
-- url     : https://prove2.me/submissions/6ad3dab2-8246-4c40-9293-5eb63ba83ca9

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_time_le_budget
import Theorems.Thm_Light_Meets_mono_time


set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDivide
open Light Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}
namespace ThreeSum.LightOutputDecodeDivide
theorem _root_.solution {pMain : ℕ} (hmain : P[pMain]? = some body)
    (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Meets lim P pMain d [a,Mo,fr] μ (budget V)
      (fun q ν => q = ((a/Mo : ℕ) : ℤ) ∧ Kept μ ν fr) :=
  (meets hmain F haV).mono_time (time_le_budget haV)
end ThreeSum.LightOutputDecodeDivide

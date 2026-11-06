-- Prove2me | solution 1 for RH.Transport.TunedEndpoint.witness_in_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:41.187876+00:00
-- url     : https://prove2.me/submissions/dd4cfd4d-7ba9-41da-9110-fc75b3005e91

import Definitions.Def_Transport_Endpoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_TunedEndpoint

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.TunedEndpoint
noncomputable section
namespace RH.Transport.TunedEndpoint
theorem _root_.solution :
    (1 / 50 : ℝ) ≤ witnessDelta1 ∧ witnessDelta1 ≤ 3 / 4 ∧
    (1 / 50 : ℝ) ≤ witnessDelta2 ∧ witnessDelta2 ≤ 3 / 4 := by
  norm_num [witnessDelta1, witnessDelta2]
end RH.Transport.TunedEndpoint

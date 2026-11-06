-- Prove2me | solution 1 for RH.Transport.Endpoint.witness_in_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:25:13.027193+00:00
-- url     : https://prove2.me/submissions/7e25758c-0731-4889-a2f2-0859bca68c20

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Endpoint

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.Endpoint
noncomputable section
namespace RH.Transport.Endpoint
theorem _root_.solution :
    (1 / 50 : ℝ) ≤ witnessDelta ∧ witnessDelta ≤ 3 / 4 ∧
      (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 / 2 := by
  norm_num [witnessDelta]
end RH.Transport.Endpoint

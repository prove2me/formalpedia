-- Prove2me | solution 1 for RH.Transport.TunedEndpoint.strict_screen_requires_p_lt_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:49.5442+00:00
-- url     : https://prove2.me/submissions/ad10209d-f2ba-4410-b5d6-6fdd3339dbb0

import Definitions.Def_Transport_Endpoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_TunedEndpoint
import Theorems.Thm_RH_Transport_TunedEndpoint_witness_in_domain
import Theorems.Thm_RH_Transport_TunedEndpoint_beyond_screenUpper_fails
import Theorems.Thm_RH_Transport_Endpoint_beyond_screenUpper_fails
import Theorems.Thm_RH_Transport_Endpoint_witness_in_domain


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.TunedEndpoint
noncomputable section
namespace RH.Transport.TunedEndpoint
theorem _root_.solution {p b : ℝ}
    (hgood : ∀ δ x : ℝ, (1 / 50 : ℝ) ≤ δ → δ ≤ 3 / 4 →
      0 ≤ x → x ≤ 1 / 2 → generalEndpointExponent p b δ x < 0) :
    p < screenUpper := by
  by_contra hp
  have hfail := beyond_screenUpper_fails (le_of_not_gt hp) b
  obtain ⟨h1lo, h1hi, h2lo, h2hi⟩ := witness_in_domain
  exact hfail ⟨hgood witnessDelta1 (1 / 2) h1lo h1hi (by norm_num) (by norm_num),
    hgood witnessDelta2 (1 / 2) h2lo h2hi (by norm_num) (by norm_num)⟩
end RH.Transport.TunedEndpoint

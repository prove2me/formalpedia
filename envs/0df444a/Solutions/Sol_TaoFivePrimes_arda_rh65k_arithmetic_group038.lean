-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group038
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:15:47.547689+00:00
-- url     : https://prove2.me/submissions/4f4ffdb2-4dc0-4477-8ec2-d0d796687c12

import Definitions.Def_ArdaRH65K_Data038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0304.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0304.samples = 127) ∧
    (RS5.bandOK' RH65K_0305.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0305.samples = 127) ∧
    (RS5.bandOK' RH65K_0306.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0306.samples = 127) ∧
    (RS5.bandOK' RH65K_0307.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0307.samples = 127) ∧
    (RS5.bandOK' RH65K_0308.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0308.samples = 127) ∧
    (RS5.bandOK' RH65K_0309.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0309.samples = 127) ∧
    (RS5.bandOK' RH65K_0310.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0310.samples = 127) ∧
    (RS5.bandOK' RH65K_0311.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0311.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

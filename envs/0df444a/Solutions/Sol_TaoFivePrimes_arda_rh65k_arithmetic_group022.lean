-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group022
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:36:50.769281+00:00
-- url     : https://prove2.me/submissions/87444dc0-e0bd-463d-a0f2-180e1164d066

import Definitions.Def_ArdaRH65K_Data022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0176.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0176.samples = 127) ∧
    (RS5.bandOK' RH65K_0177.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0177.samples = 127) ∧
    (RS5.bandOK' RH65K_0178.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0178.samples = 127) ∧
    (RS5.bandOK' RH65K_0179.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0179.samples = 127) ∧
    (RS5.bandOK' RH65K_0180.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0180.samples = 127) ∧
    (RS5.bandOK' RH65K_0181.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0181.samples = 127) ∧
    (RS5.bandOK' RH65K_0182.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0182.samples = 127) ∧
    (RS5.bandOK' RH65K_0183.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0183.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

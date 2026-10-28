-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group017
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:26:03.125423+00:00
-- url     : https://prove2.me/submissions/80a81650-55e3-4240-9966-b99b7966e510

import Definitions.Def_ArdaRH65K_Data017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0136.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0136.samples = 127) ∧
    (RS5.bandOK' RH65K_0137.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0137.samples = 127) ∧
    (RS5.bandOK' RH65K_0138.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0138.samples = 127) ∧
    (RS5.bandOK' RH65K_0139.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0139.samples = 127) ∧
    (RS5.bandOK' RH65K_0140.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0140.samples = 127) ∧
    (RS5.bandOK' RH65K_0141.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0141.samples = 127) ∧
    (RS5.bandOK' RH65K_0142.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0142.samples = 127) ∧
    (RS5.bandOK' RH65K_0143.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0143.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group045
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:35:21.470819+00:00
-- url     : https://prove2.me/submissions/07f0e6da-ac66-430b-b7be-0929b2cf4f8c

import Definitions.Def_ArdaRH65K_Data045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0360.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0360.samples = 127) ∧
    (RS5.bandOK' RH65K_0361.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0361.samples = 127) ∧
    (RS5.bandOK' RH65K_0362.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0362.samples = 127) ∧
    (RS5.bandOK' RH65K_0363.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0363.samples = 127) ∧
    (RS5.bandOK' RH65K_0364.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0364.samples = 127) ∧
    (RS5.bandOK' RH65K_0365.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0365.samples = 127) ∧
    (RS5.bandOK' RH65K_0366.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0366.samples = 127) ∧
    (RS5.bandOK' RH65K_0367.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0367.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

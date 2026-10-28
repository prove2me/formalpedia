-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_low_arithmetic_group009
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:43:32.13104+00:00
-- url     : https://prove2.me/submissions/c5e4507f-b4a2-4cb3-8b2c-8e3ba5cfa3b0

import Definitions.Def_ArdaRH65K_LowData009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_Low_0072.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0072.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0073.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0073.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0074.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0074.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0075.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0075.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0076.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0076.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0077.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0077.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0078.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0078.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0079.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0079.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

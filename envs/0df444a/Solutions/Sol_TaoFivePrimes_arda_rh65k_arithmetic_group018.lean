-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group018
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:28:58.281309+00:00
-- url     : https://prove2.me/submissions/a8d9fde0-43c5-450c-a95e-3086fede70a1

import Definitions.Def_ArdaRH65K_Data018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0144.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0144.samples = 127) ∧
    (RS5.bandOK' RH65K_0145.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0145.samples = 127) ∧
    (RS5.bandOK' RH65K_0146.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0146.samples = 127) ∧
    (RS5.bandOK' RH65K_0147.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0147.samples = 127) ∧
    (RS5.bandOK' RH65K_0148.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0148.samples = 127) ∧
    (RS5.bandOK' RH65K_0149.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0149.samples = 127) ∧
    (RS5.bandOK' RH65K_0150.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0150.samples = 127) ∧
    (RS5.bandOK' RH65K_0151.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0151.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

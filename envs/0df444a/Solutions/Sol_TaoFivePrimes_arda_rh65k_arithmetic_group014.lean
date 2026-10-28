-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group014
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:19:22.299733+00:00
-- url     : https://prove2.me/submissions/ad28c3dc-2cda-4d39-ba14-1f40e4d89914

import Definitions.Def_ArdaRH65K_Data014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0112.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0112.samples = 127) ∧
    (RS5.bandOK' RH65K_0113.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0113.samples = 127) ∧
    (RS5.bandOK' RH65K_0114.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0114.samples = 127) ∧
    (RS5.bandOK' RH65K_0115.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0115.samples = 127) ∧
    (RS5.bandOK' RH65K_0116.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0116.samples = 127) ∧
    (RS5.bandOK' RH65K_0117.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0117.samples = 127) ∧
    (RS5.bandOK' RH65K_0118.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0118.samples = 127) ∧
    (RS5.bandOK' RH65K_0119.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0119.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_bridge_arithmetic_group000
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:08:07.646093+00:00
-- url     : https://prove2.me/submissions/37149c0e-be48-44a6-912c-5b9ebff22451

import Definitions.Def_ArdaRH65K_BridgeData000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK RH65K_Bridge_0000.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Bridge_0000.samples = 127) ∧
    (RS5.bandOK RH65K_Bridge_0001.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Bridge_0001.samples = 127) ∧
    (RS5.bandOK RH65K_Bridge_0002.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Bridge_0002.samples = 112) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

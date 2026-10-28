-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_low_arithmetic_group005
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:29:30.863567+00:00
-- url     : https://prove2.me/submissions/736c6d75-9feb-4d7a-8e6a-73d81a4cd4e9

import Definitions.Def_ArdaRH65K_LowData005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_Low_0040.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0040.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0041.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0041.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0042.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0042.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0043.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0043.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0044.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0044.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0045.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0045.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0046.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0046.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0047.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0047.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

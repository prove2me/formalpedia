-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group005
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:02:32.451994+00:00
-- url     : https://prove2.me/submissions/d11befac-9d3a-4e83-b313-84ff20a92e30

import Definitions.Def_ArdaRH65K_Data005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0040.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0040.samples = 127) ∧
    (RS5.bandOK' RH65K_0041.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0041.samples = 127) ∧
    (RS5.bandOK' RH65K_0042.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0042.samples = 127) ∧
    (RS5.bandOK' RH65K_0043.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0043.samples = 127) ∧
    (RS5.bandOK' RH65K_0044.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0044.samples = 127) ∧
    (RS5.bandOK' RH65K_0045.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0045.samples = 127) ∧
    (RS5.bandOK' RH65K_0046.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0046.samples = 127) ∧
    (RS5.bandOK' RH65K_0047.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0047.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

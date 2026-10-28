-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group037
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:14:12.578364+00:00
-- url     : https://prove2.me/submissions/f5df3172-dfd7-40e4-8e36-47edbbd78c74

import Definitions.Def_ArdaRH65K_Data037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0296.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0296.samples = 127) ∧
    (RS5.bandOK' RH65K_0297.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0297.samples = 127) ∧
    (RS5.bandOK' RH65K_0298.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0298.samples = 127) ∧
    (RS5.bandOK' RH65K_0299.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0299.samples = 127) ∧
    (RS5.bandOK' RH65K_0300.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0300.samples = 127) ∧
    (RS5.bandOK' RH65K_0301.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0301.samples = 127) ∧
    (RS5.bandOK' RH65K_0302.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0302.samples = 127) ∧
    (RS5.bandOK' RH65K_0303.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0303.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group043
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:28:43.629181+00:00
-- url     : https://prove2.me/submissions/2f792f86-0947-47ba-9f6b-855d8f29f03b

import Definitions.Def_ArdaRH65K_Data043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0344.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0344.samples = 127) ∧
    (RS5.bandOK' RH65K_0345.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0345.samples = 127) ∧
    (RS5.bandOK' RH65K_0346.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0346.samples = 127) ∧
    (RS5.bandOK' RH65K_0347.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0347.samples = 127) ∧
    (RS5.bandOK' RH65K_0348.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0348.samples = 127) ∧
    (RS5.bandOK' RH65K_0349.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0349.samples = 127) ∧
    (RS5.bandOK' RH65K_0350.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0350.samples = 127) ∧
    (RS5.bandOK' RH65K_0351.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0351.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group041
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:23:27.872291+00:00
-- url     : https://prove2.me/submissions/6f41b7ea-8d65-49b7-adbf-5750dd55b8b2

import Definitions.Def_ArdaRH65K_Data041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0328.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0328.samples = 127) ∧
    (RS5.bandOK' RH65K_0329.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0329.samples = 127) ∧
    (RS5.bandOK' RH65K_0330.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0330.samples = 127) ∧
    (RS5.bandOK' RH65K_0331.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0331.samples = 127) ∧
    (RS5.bandOK' RH65K_0332.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0332.samples = 127) ∧
    (RS5.bandOK' RH65K_0333.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0333.samples = 127) ∧
    (RS5.bandOK' RH65K_0334.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0334.samples = 127) ∧
    (RS5.bandOK' RH65K_0335.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0335.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

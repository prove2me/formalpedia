-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group004
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:00:37.426335+00:00
-- url     : https://prove2.me/submissions/b06c19c9-4567-41d7-bdee-8e7386869300

import Definitions.Def_ArdaRH65K_Data004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0032.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0032.samples = 127) ∧
    (RS5.bandOK' RH65K_0033.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0033.samples = 127) ∧
    (RS5.bandOK' RH65K_0034.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0034.samples = 127) ∧
    (RS5.bandOK' RH65K_0035.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0035.samples = 127) ∧
    (RS5.bandOK' RH65K_0036.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0036.samples = 127) ∧
    (RS5.bandOK' RH65K_0037.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0037.samples = 127) ∧
    (RS5.bandOK' RH65K_0038.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0038.samples = 127) ∧
    (RS5.bandOK' RH65K_0039.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0039.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

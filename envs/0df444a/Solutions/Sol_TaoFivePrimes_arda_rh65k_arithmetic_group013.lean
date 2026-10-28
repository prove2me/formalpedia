-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group013
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:18:17.645378+00:00
-- url     : https://prove2.me/submissions/9d31c0ef-175b-46a0-9eb1-04dacb4da3c8

import Definitions.Def_ArdaRH65K_Data013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0104.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0104.samples = 127) ∧
    (RS5.bandOK' RH65K_0105.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0105.samples = 127) ∧
    (RS5.bandOK' RH65K_0106.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0106.samples = 127) ∧
    (RS5.bandOK' RH65K_0107.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0107.samples = 127) ∧
    (RS5.bandOK' RH65K_0108.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0108.samples = 127) ∧
    (RS5.bandOK' RH65K_0109.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0109.samples = 127) ∧
    (RS5.bandOK' RH65K_0110.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0110.samples = 127) ∧
    (RS5.bandOK' RH65K_0111.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0111.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

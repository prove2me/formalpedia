-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group015
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:22:45.146702+00:00
-- url     : https://prove2.me/submissions/8b47af8c-d24a-4e9f-a315-a357985f9586

import Definitions.Def_ArdaRH65K_Data015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0120.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0120.samples = 127) ∧
    (RS5.bandOK' RH65K_0121.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0121.samples = 127) ∧
    (RS5.bandOK' RH65K_0122.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0122.samples = 127) ∧
    (RS5.bandOK' RH65K_0123.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0123.samples = 127) ∧
    (RS5.bandOK' RH65K_0124.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0124.samples = 127) ∧
    (RS5.bandOK' RH65K_0125.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0125.samples = 127) ∧
    (RS5.bandOK' RH65K_0126.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0126.samples = 127) ∧
    (RS5.bandOK' RH65K_0127.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0127.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

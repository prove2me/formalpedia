-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group051
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:53:51.584186+00:00
-- url     : https://prove2.me/submissions/e8187838-d726-49f7-9219-2cd25aa598e2

import Definitions.Def_ArdaRH65K_Data051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0408.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0408.samples = 127) ∧
    (RS5.bandOK' RH65K_0409.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0409.samples = 127) ∧
    (RS5.bandOK' RH65K_0410.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0410.samples = 127) ∧
    (RS5.bandOK' RH65K_0411.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0411.samples = 127) ∧
    (RS5.bandOK' RH65K_0412.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0412.samples = 127) ∧
    (RS5.bandOK' RH65K_0413.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0413.samples = 127) ∧
    (RS5.bandOK' RH65K_0414.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0414.samples = 127) ∧
    (RS5.bandOK' RH65K_0415.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0415.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

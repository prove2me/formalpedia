-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group023
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:38:32.407857+00:00
-- url     : https://prove2.me/submissions/160bddd2-438f-4aaa-b4af-a6cfeb9f363f

import Definitions.Def_ArdaRH65K_Data023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0184.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0184.samples = 127) ∧
    (RS5.bandOK' RH65K_0185.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0185.samples = 127) ∧
    (RS5.bandOK' RH65K_0186.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0186.samples = 127) ∧
    (RS5.bandOK' RH65K_0187.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0187.samples = 127) ∧
    (RS5.bandOK' RH65K_0188.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0188.samples = 127) ∧
    (RS5.bandOK' RH65K_0189.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0189.samples = 127) ∧
    (RS5.bandOK' RH65K_0190.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0190.samples = 127) ∧
    (RS5.bandOK' RH65K_0191.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0191.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

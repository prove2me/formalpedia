-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group042
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:26:47.053561+00:00
-- url     : https://prove2.me/submissions/f8c228b4-4211-493c-a8ff-d620daca082a

import Definitions.Def_ArdaRH65K_Data042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0336.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0336.samples = 127) ∧
    (RS5.bandOK' RH65K_0337.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0337.samples = 127) ∧
    (RS5.bandOK' RH65K_0338.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0338.samples = 127) ∧
    (RS5.bandOK' RH65K_0339.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0339.samples = 127) ∧
    (RS5.bandOK' RH65K_0340.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0340.samples = 127) ∧
    (RS5.bandOK' RH65K_0341.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0341.samples = 127) ∧
    (RS5.bandOK' RH65K_0342.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0342.samples = 127) ∧
    (RS5.bandOK' RH65K_0343.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0343.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

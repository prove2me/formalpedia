-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group058
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T04:14:21.372136+00:00
-- url     : https://prove2.me/submissions/ef0a4623-4643-48a1-81ed-54364a08248c

import Definitions.Def_ArdaRH65K_Data058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0464.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0464.samples = 127) ∧
    (RS5.bandOK' RH65K_0465.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0465.samples = 127) ∧
    (RS5.bandOK' RH65K_0466.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0466.samples = 127) ∧
    (RS5.bandOK' RH65K_0467.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0467.samples = 127) ∧
    (RS5.bandOK' RH65K_0468.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0468.samples = 127) ∧
    (RS5.bandOK' RH65K_0469.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0469.samples = 127) ∧
    (RS5.bandOK' RH65K_0470.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0470.samples = 127) ∧
    (RS5.bandOK' RH65K_0471.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0471.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

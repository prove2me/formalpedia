-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group047
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:41:20.505605+00:00
-- url     : https://prove2.me/submissions/a3ac0fd7-34a3-47e4-b3c5-a10f1355cd3f

import Definitions.Def_ArdaRH65K_Data047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0376.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0376.samples = 127) ∧
    (RS5.bandOK' RH65K_0377.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0377.samples = 127) ∧
    (RS5.bandOK' RH65K_0378.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0378.samples = 127) ∧
    (RS5.bandOK' RH65K_0379.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0379.samples = 127) ∧
    (RS5.bandOK' RH65K_0380.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0380.samples = 127) ∧
    (RS5.bandOK' RH65K_0381.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0381.samples = 127) ∧
    (RS5.bandOK' RH65K_0382.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0382.samples = 127) ∧
    (RS5.bandOK' RH65K_0383.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0383.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

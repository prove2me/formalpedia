-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group036
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:11:36.394807+00:00
-- url     : https://prove2.me/submissions/3198a1b2-bec3-4ff8-92d1-e332e191990b

import Definitions.Def_ArdaRH65K_Data036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0288.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0288.samples = 127) ∧
    (RS5.bandOK' RH65K_0289.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0289.samples = 127) ∧
    (RS5.bandOK' RH65K_0290.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0290.samples = 127) ∧
    (RS5.bandOK' RH65K_0291.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0291.samples = 127) ∧
    (RS5.bandOK' RH65K_0292.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0292.samples = 127) ∧
    (RS5.bandOK' RH65K_0293.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0293.samples = 127) ∧
    (RS5.bandOK' RH65K_0294.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0294.samples = 127) ∧
    (RS5.bandOK' RH65K_0295.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0295.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

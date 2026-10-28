-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group055
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T04:07:13.498143+00:00
-- url     : https://prove2.me/submissions/05c662fc-cf74-4d4f-9c29-4098fb23b3d3

import Definitions.Def_ArdaRH65K_Data055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0440.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0440.samples = 127) ∧
    (RS5.bandOK' RH65K_0441.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0441.samples = 127) ∧
    (RS5.bandOK' RH65K_0442.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0442.samples = 127) ∧
    (RS5.bandOK' RH65K_0443.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0443.samples = 127) ∧
    (RS5.bandOK' RH65K_0444.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0444.samples = 127) ∧
    (RS5.bandOK' RH65K_0445.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0445.samples = 127) ∧
    (RS5.bandOK' RH65K_0446.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0446.samples = 127) ∧
    (RS5.bandOK' RH65K_0447.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0447.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

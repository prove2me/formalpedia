-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group050
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:51:07.182+00:00
-- url     : https://prove2.me/submissions/ca3f0760-299d-457e-8b17-f57151b964e9

import Definitions.Def_ArdaRH65K_Data050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0400.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0400.samples = 127) ∧
    (RS5.bandOK' RH65K_0401.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0401.samples = 127) ∧
    (RS5.bandOK' RH65K_0402.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0402.samples = 127) ∧
    (RS5.bandOK' RH65K_0403.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0403.samples = 127) ∧
    (RS5.bandOK' RH65K_0404.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0404.samples = 127) ∧
    (RS5.bandOK' RH65K_0405.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0405.samples = 127) ∧
    (RS5.bandOK' RH65K_0406.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0406.samples = 127) ∧
    (RS5.bandOK' RH65K_0407.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0407.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

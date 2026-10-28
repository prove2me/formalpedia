-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_low_arithmetic_group003
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:17:49.841386+00:00
-- url     : https://prove2.me/submissions/7d456221-bd8d-441f-9075-49529dc247a7

import Definitions.Def_ArdaRH65K_LowData003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK RH65K_Low_0024.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0024.samples = 36) ∧
    (RS5.bandOK' RH65K_Low_0025.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0025.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0026.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0026.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0027.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0027.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0028.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0028.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0029.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0029.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0030.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0030.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0031.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0031.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

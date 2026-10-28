-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_low_arithmetic_group001
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:09:15.74835+00:00
-- url     : https://prove2.me/submissions/91482e8c-7693-4d8a-8df1-bd8bbcf0175e

import Definitions.Def_ArdaRH65K_LowData001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK RH65K_Low_0008.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0008.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0009.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0009.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0010.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0010.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0011.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0011.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0012.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0012.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0013.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0013.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0014.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0014.samples = 127) ∧
    (RS5.bandOK RH65K_Low_0015.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0015.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

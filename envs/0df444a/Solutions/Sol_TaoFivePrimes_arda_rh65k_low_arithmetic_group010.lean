-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_low_arithmetic_group010
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:46:19.061442+00:00
-- url     : https://prove2.me/submissions/6c5e66cc-23ff-40c7-b37b-849e48020dfd

import Definitions.Def_ArdaRH65K_LowData010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_Low_0080.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0080.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0081.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0081.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0082.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0082.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0083.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0083.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0084.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0084.samples = 103) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group026
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:47:01.775991+00:00
-- url     : https://prove2.me/submissions/640d71de-a3d8-4855-b6d0-d13214462bd7

import Definitions.Def_ArdaRH65K_Data026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0208.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0208.samples = 127) ∧
    (RS5.bandOK' RH65K_0209.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0209.samples = 127) ∧
    (RS5.bandOK' RH65K_0210.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0210.samples = 127) ∧
    (RS5.bandOK' RH65K_0211.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0211.samples = 127) ∧
    (RS5.bandOK' RH65K_0212.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0212.samples = 127) ∧
    (RS5.bandOK' RH65K_0213.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0213.samples = 127) ∧
    (RS5.bandOK' RH65K_0214.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0214.samples = 127) ∧
    (RS5.bandOK' RH65K_0215.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0215.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

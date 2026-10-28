-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_low_arithmetic_group008
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:39:16.231493+00:00
-- url     : https://prove2.me/submissions/d49ce7d6-acb4-4553-b7d0-16f4fea0c87a

import Definitions.Def_ArdaRH65K_LowData008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_Low_0064.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0064.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0065.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0065.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0066.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0066.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0067.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0067.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0068.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0068.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0069.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0069.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0070.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0070.samples = 127) ∧
    (RS5.bandOK' RH65K_Low_0071.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_Low_0071.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

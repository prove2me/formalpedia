-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group020
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:32:14.649996+00:00
-- url     : https://prove2.me/submissions/37dfc084-2bba-4f8e-b3ca-8051ae7e69c9

import Definitions.Def_ArdaRH65K_Data020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0160.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0160.samples = 127) ∧
    (RS5.bandOK' RH65K_0161.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0161.samples = 127) ∧
    (RS5.bandOK' RH65K_0162.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0162.samples = 127) ∧
    (RS5.bandOK' RH65K_0163.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0163.samples = 127) ∧
    (RS5.bandOK' RH65K_0164.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0164.samples = 127) ∧
    (RS5.bandOK' RH65K_0165.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0165.samples = 127) ∧
    (RS5.bandOK' RH65K_0166.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0166.samples = 127) ∧
    (RS5.bandOK' RH65K_0167.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0167.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

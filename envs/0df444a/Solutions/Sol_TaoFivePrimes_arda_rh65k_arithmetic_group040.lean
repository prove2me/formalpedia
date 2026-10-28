-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group040
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:21:24.659993+00:00
-- url     : https://prove2.me/submissions/d81deb7a-cf12-4435-b8ed-6a7571473048

import Definitions.Def_ArdaRH65K_Data040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0320.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0320.samples = 127) ∧
    (RS5.bandOK' RH65K_0321.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0321.samples = 127) ∧
    (RS5.bandOK' RH65K_0322.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0322.samples = 127) ∧
    (RS5.bandOK' RH65K_0323.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0323.samples = 127) ∧
    (RS5.bandOK' RH65K_0324.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0324.samples = 127) ∧
    (RS5.bandOK' RH65K_0325.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0325.samples = 127) ∧
    (RS5.bandOK' RH65K_0326.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0326.samples = 127) ∧
    (RS5.bandOK' RH65K_0327.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0327.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

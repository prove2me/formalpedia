-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group019
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:30:42.969908+00:00
-- url     : https://prove2.me/submissions/579af9c0-42eb-4afe-9286-7a225647b8b8

import Definitions.Def_ArdaRH65K_Data019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0152.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0152.samples = 127) ∧
    (RS5.bandOK' RH65K_0153.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0153.samples = 127) ∧
    (RS5.bandOK' RH65K_0154.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0154.samples = 127) ∧
    (RS5.bandOK' RH65K_0155.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0155.samples = 127) ∧
    (RS5.bandOK' RH65K_0156.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0156.samples = 127) ∧
    (RS5.bandOK' RH65K_0157.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0157.samples = 127) ∧
    (RS5.bandOK' RH65K_0158.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0158.samples = 127) ∧
    (RS5.bandOK' RH65K_0159.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0159.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

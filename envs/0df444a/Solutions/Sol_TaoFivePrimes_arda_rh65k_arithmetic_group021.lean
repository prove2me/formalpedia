-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group021
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:34:55.660834+00:00
-- url     : https://prove2.me/submissions/bff00013-ef58-4c25-838a-4a2095cb05a4

import Definitions.Def_ArdaRH65K_Data021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0168.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0168.samples = 127) ∧
    (RS5.bandOK' RH65K_0169.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0169.samples = 127) ∧
    (RS5.bandOK' RH65K_0170.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0170.samples = 127) ∧
    (RS5.bandOK' RH65K_0171.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0171.samples = 127) ∧
    (RS5.bandOK' RH65K_0172.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0172.samples = 127) ∧
    (RS5.bandOK' RH65K_0173.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0173.samples = 127) ∧
    (RS5.bandOK' RH65K_0174.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0174.samples = 127) ∧
    (RS5.bandOK' RH65K_0175.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0175.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group003
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:59:07.673992+00:00
-- url     : https://prove2.me/submissions/efd832cc-2c88-4af7-9abe-5dc577854d59

import Definitions.Def_ArdaRH65K_Data003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0024.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0024.samples = 127) ∧
    (RS5.bandOK' RH65K_0025.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0025.samples = 127) ∧
    (RS5.bandOK' RH65K_0026.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0026.samples = 127) ∧
    (RS5.bandOK' RH65K_0027.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0027.samples = 127) ∧
    (RS5.bandOK' RH65K_0028.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0028.samples = 127) ∧
    (RS5.bandOK' RH65K_0029.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0029.samples = 127) ∧
    (RS5.bandOK' RH65K_0030.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0030.samples = 127) ∧
    (RS5.bandOK' RH65K_0031.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0031.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

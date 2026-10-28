-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group039
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:18:46.80363+00:00
-- url     : https://prove2.me/submissions/b10c4c24-6e66-406a-9928-108f3fb49f05

import Definitions.Def_ArdaRH65K_Data039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0312.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0312.samples = 127) ∧
    (RS5.bandOK' RH65K_0313.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0313.samples = 127) ∧
    (RS5.bandOK' RH65K_0314.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0314.samples = 127) ∧
    (RS5.bandOK' RH65K_0315.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0315.samples = 127) ∧
    (RS5.bandOK' RH65K_0316.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0316.samples = 127) ∧
    (RS5.bandOK' RH65K_0317.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0317.samples = 127) ∧
    (RS5.bandOK' RH65K_0318.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0318.samples = 127) ∧
    (RS5.bandOK' RH65K_0319.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0319.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

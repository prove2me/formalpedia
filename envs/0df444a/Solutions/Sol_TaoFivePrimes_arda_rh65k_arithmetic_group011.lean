-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group011
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:13:24.112717+00:00
-- url     : https://prove2.me/submissions/f515e9bd-51b5-4c55-b6e8-cebeadbac651

import Definitions.Def_ArdaRH65K_Data011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0088.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0088.samples = 127) ∧
    (RS5.bandOK' RH65K_0089.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0089.samples = 127) ∧
    (RS5.bandOK' RH65K_0090.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0090.samples = 127) ∧
    (RS5.bandOK' RH65K_0091.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0091.samples = 127) ∧
    (RS5.bandOK' RH65K_0092.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0092.samples = 127) ∧
    (RS5.bandOK' RH65K_0093.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0093.samples = 127) ∧
    (RS5.bandOK' RH65K_0094.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0094.samples = 127) ∧
    (RS5.bandOK' RH65K_0095.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0095.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

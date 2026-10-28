-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group002
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:57:16.598263+00:00
-- url     : https://prove2.me/submissions/e6a095f3-a08e-4500-84d2-8750ce894675

import Definitions.Def_ArdaRH65K_Data002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0016.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0016.samples = 127) ∧
    (RS5.bandOK' RH65K_0017.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0017.samples = 127) ∧
    (RS5.bandOK' RH65K_0018.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0018.samples = 127) ∧
    (RS5.bandOK' RH65K_0019.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0019.samples = 127) ∧
    (RS5.bandOK' RH65K_0020.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0020.samples = 127) ∧
    (RS5.bandOK' RH65K_0021.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0021.samples = 127) ∧
    (RS5.bandOK' RH65K_0022.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0022.samples = 127) ∧
    (RS5.bandOK' RH65K_0023.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0023.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

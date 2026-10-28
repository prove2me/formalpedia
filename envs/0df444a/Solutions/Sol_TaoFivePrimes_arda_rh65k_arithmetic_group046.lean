-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group046
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:37:56.006006+00:00
-- url     : https://prove2.me/submissions/661797b5-7520-4efc-98c1-80553df77c23

import Definitions.Def_ArdaRH65K_Data046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0368.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0368.samples = 127) ∧
    (RS5.bandOK' RH65K_0369.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0369.samples = 127) ∧
    (RS5.bandOK' RH65K_0370.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0370.samples = 127) ∧
    (RS5.bandOK' RH65K_0371.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0371.samples = 127) ∧
    (RS5.bandOK' RH65K_0372.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0372.samples = 127) ∧
    (RS5.bandOK' RH65K_0373.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0373.samples = 127) ∧
    (RS5.bandOK' RH65K_0374.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0374.samples = 127) ∧
    (RS5.bandOK' RH65K_0375.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0375.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

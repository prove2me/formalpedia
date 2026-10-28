-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group010
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T02:11:52.336324+00:00
-- url     : https://prove2.me/submissions/b4a62a9a-6376-4d73-b403-b0a91cb82c1e

import Definitions.Def_ArdaRH65K_Data010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0080.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0080.samples = 127) ∧
    (RS5.bandOK' RH65K_0081.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0081.samples = 127) ∧
    (RS5.bandOK' RH65K_0082.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0082.samples = 127) ∧
    (RS5.bandOK' RH65K_0083.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0083.samples = 127) ∧
    (RS5.bandOK' RH65K_0084.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0084.samples = 127) ∧
    (RS5.bandOK' RH65K_0085.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0085.samples = 127) ∧
    (RS5.bandOK' RH65K_0086.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0086.samples = 127) ∧
    (RS5.bandOK' RH65K_0087.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0087.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.arda_rh65k_arithmetic_group052
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:56:09.242764+00:00
-- url     : https://prove2.me/submissions/2bcc0019-1ccd-4ac0-a388-6e0c7ae3908d

import Definitions.Def_ArdaRH65K_Data052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution :
    (RS5.bandOK' RH65K_0416.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0416.samples = 127) ∧
    (RS5.bandOK' RH65K_0417.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0417.samples = 127) ∧
    (RS5.bandOK' RH65K_0418.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0418.samples = 127) ∧
    (RS5.bandOK' RH65K_0419.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0419.samples = 127) ∧
    (RS5.bandOK' RH65K_0420.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0420.samples = 127) ∧
    (RS5.bandOK' RH65K_0421.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0421.samples = 127) ∧
    (RS5.bandOK' RH65K_0422.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0422.samples = 127) ∧
    (RS5.bandOK' RH65K_0423.samples = true ∧ RS5.chgBy RS5.Sample.pos RH65K_0423.samples = 127) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals decide +kernel

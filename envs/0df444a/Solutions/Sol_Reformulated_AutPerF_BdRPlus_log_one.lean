-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.log_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T03:19:06.064506+00:00
-- url     : https://prove2.me/submissions/1c60520e-9738-487c-98c9-0d85847627d8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal Polynomial
open Reformulated Reformulated.AutPerF
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Reformulated.AutPerF.BdRPlus
theorem solution : log (1 : BdRPlus p R) (map_one _) = 0 := by
  show adicLog (AinfInv.kerTheta p R) (1 : AdicCompletion (AinfInv.kerTheta p R) (AinfInv p R)) _ = 0
  apply AdicCompletion.ext_evalₐ
  intro n
  unfold adicLog
  rw [evalₐ_adicMk, sub_self, map_zero]
  simp [truncLog]

-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.fil_eq_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:06.149926+00:00
-- url     : https://prove2.me/submissions/1078f4c9-df40-45f7-bda4-6a30481515bd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdRPlus
variable [IsAlgClosed (FractionRing R)]
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution (n : ℕ) :
    fil p R n = IsLocalRing.maximalIdeal (BdRPlus p R) ^ n := by rw [fil, maximalIdeal_eq]
end Reformulated.AutPerF.BdRPlus

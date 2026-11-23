-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.algebraMap_away_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:48.198945+00:00
-- url     : https://prove2.me/submissions/f43a158e-32f3-464f-95a1-1ddc0ad4bd64

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel

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
open Reformulated.AutPerF.AinfInv
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] [ValuationRing R]
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution :
    Function.Injective (algebraMap R (Localization.Away (p : R))) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors
    (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
end Reformulated.AutPerF.AinfInv

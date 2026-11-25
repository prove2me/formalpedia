-- Prove2me | solution 1 for Reformulated.AutPerF.BcrisPlus.algebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:15.711854+00:00
-- url     : https://prove2.me/submissions/48778621-ea90-4e12-9ef8-04a7beec29b6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero

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
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.BcrisPlus
namespace Reformulated.AutPerF.BcrisPlus
theorem _root_.solution : Function.Injective (algebraMap (Acris p R) (BcrisPlus p R)) :=
  IsLocalization.injective (M := Submonoid.powers (p : Acris p R)) _
    (Submonoid.powers_le.2 Acris.p_mem_nonZeroDivisors)
end Reformulated.AutPerF.BcrisPlus

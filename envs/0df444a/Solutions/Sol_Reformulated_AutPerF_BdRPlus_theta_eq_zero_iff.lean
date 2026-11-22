-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.theta_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:00:57.88331+00:00
-- url     : https://prove2.me/submissions/30ad4551-e740-4ea8-8894-0e0fe7513162

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero

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
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.BdRPlus
variable {p R}
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution (x : BdRPlus p R) :
    theta p R x = 0 ↔ AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) x = 0 :=
  map_eq_zero_iff _ (RingHom.kerLift_injective _)
end Reformulated.AutPerF.BdRPlus

-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.ext_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:59:19.666311+00:00
-- url     : https://prove2.me/submissions/f6756417-689e-4367-b336-f6e9505d9ad1

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
open Reformulated.AutPerF.Acris
variable {p R}
namespace Reformulated.AutPerF.Acris
theorem _root_.solution {x y : Acris p R} (h : ∀ n, eval p R n x = eval p R n y) : x = y :=
  AdicCompletion.ext_evalₐ h
end Reformulated.AutPerF.Acris

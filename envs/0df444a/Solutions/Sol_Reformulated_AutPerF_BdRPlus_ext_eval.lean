-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.ext_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:59:18.981991+00:00
-- url     : https://prove2.me/submissions/714df673-7d8f-420b-96e1-b7ad1e0fa4e8

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
theorem _root_.solution {x y : BdRPlus p R} (h : ∀ n, eval p R n x = eval p R n y) : x = y :=
  AdicCompletion.ext_evalₐ h
end Reformulated.AutPerF.BdRPlus

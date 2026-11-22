-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.eval_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:40.925964+00:00
-- url     : https://prove2.me/submissions/d1b7a4ad-a12e-472b-bfde-280119e0ea25

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
theorem _root_.solution (u : Ainf p R) (hu : Ainf.theta p R u = 1) {n N : ℕ} (hN : p ^ n ≤ N) :
    eval p R n (log u hu) = Ideal.Quotient.mk _ (logPartial N u hu) :=
  (evalₐ_adicMk _ _ _ n).trans (Ideal.Quotient.eq.2 (logPartial_sub_mem u hu le_rfl hN)).symm
end Reformulated.AutPerF.Acris

-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.eval_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:30.848431+00:00
-- url     : https://prove2.me/submissions/0efd09c7-4bbd-4493-b658-ded2e8a3604d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Theorems.Thm_P2M_Reformulated_AutPerF_eval__adicLog_f7990fb6ad72

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
theorem _root_.solution (u : BdRPlus p R) (hu : theta p R u = 1) (n : ℕ) :
    eval p R n (log u hu) = truncLog n (eval p R n (u - 1)) :=
  evalₐ_adicLog _ _ _ n
end Reformulated.AutPerF.BdRPlus

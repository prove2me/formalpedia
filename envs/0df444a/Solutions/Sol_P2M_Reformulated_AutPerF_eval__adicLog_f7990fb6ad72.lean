-- Prove2me | solution 1 for P2M_Reformulated_AutPerF_eval__adicLog_f7990fb6ad72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:58.285232+00:00
-- url     : https://prove2.me/submissions/bdca08e4-5596-42e9-8daf-8a192b108ad8

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
variable {A : Type u} [CommRing A]
namespace Reformulated.AutPerF
theorem _root_.solution [Algebra ℚ A] (I : Ideal A) (u : AdicCompletion I A)
    (hu : AdicCompletion.evalOneₐ I u = 1) (n : ℕ) :
    AdicCompletion.evalₐ I n (adicLog I u hu) = truncLog n (AdicCompletion.evalₐ I n (u - 1)) :=
  evalₐ_adicMk _ _ _ _
end Reformulated.AutPerF

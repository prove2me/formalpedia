-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.eq_bDeRhamPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:32:49.253206+00:00
-- url     : https://prove2.me/submissions/a9ce0636-aeb5-427f-9779-e9f8c89c999e

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
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution : BdRPlus p R = BDeRhamPlus R p := rfl
end Reformulated.AutPerF.BdRPlus

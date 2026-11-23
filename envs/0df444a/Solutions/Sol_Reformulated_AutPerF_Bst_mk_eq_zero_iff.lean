-- Prove2me | solution 1 for Reformulated.AutPerF.Bst.mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:08.728791+00:00
-- url     : https://prove2.me/submissions/2d9cd909-f2ba-4888-ab25-2c1ad835a27a

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
open Reformulated.AutPerF.Bst
variable {p R}
namespace Reformulated.AutPerF.Bst
theorem _root_.solution (f : MvPolynomial (PFlat p R) (Bcris p R)) :
    mk p R f = 0 ↔ f ∈ Bst.relations p R := Ideal.Quotient.eq_zero_iff_mem
end Reformulated.AutPerF.Bst

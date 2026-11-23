-- Prove2me | solution 1 for Reformulated.AutPerF.formallyEtale_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:56.62526+00:00
-- url     : https://prove2.me/submissions/16414dac-5031-4cb8-b3cd-4f2d0157d890

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section

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
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable [IsAdicComplete (span {(p : R)}) R]
namespace Reformulated.AutPerF
theorem _root_.solution (F : Type v) (L : Type w) [Field F] [Field L] [Algebra F L]
    [CharZero F] [Algebra.IsAlgebraic F L] : Algebra.FormallyEtale F L :=
  Algebra.FormallyEtale.of_isSeparable F L
end Reformulated.AutPerF

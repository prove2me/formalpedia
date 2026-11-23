-- Prove2me | solution 1 for Reformulated.AutPerF.tateRoot_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:06.085975+00:00
-- url     : https://prove2.me/submissions/9d9ed5f6-d78b-4fd1-b9ac-80b9dd0e050c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel

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
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
namespace Reformulated.AutPerF
theorem _root_.solution (η : tateModule p R) : tateRoot η ^ p = η.1 :=
  frobeniusEquiv_symm_pow_p (Tilt p R) p η.1
end Reformulated.AutPerF

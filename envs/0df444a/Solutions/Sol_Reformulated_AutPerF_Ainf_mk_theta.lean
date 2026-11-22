-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.mk_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:43.150799+00:00
-- url     : https://prove2.me/submissions/ad0566d4-2145-4f5d-80a2-61fe58fdcaf5

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
open Reformulated.AutPerF.Ainf
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (x : Ainf p R) : Ideal.Quotient.mk (span {(p : R)}) (theta p R x) =
    Ideal.Quotient.mk _ (PreTilt.untilt (x.coeff 0)) := by
  rw [PreTilt.mk_untilt_eq_coeff_zero]; exact WittVector.mk_fontaineTheta x
end Reformulated.AutPerF.Ainf

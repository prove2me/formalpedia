-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.isUnit_iff_isUnit_untilt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:17.615531+00:00
-- url     : https://prove2.me/submissions/2ad5b9f6-a677-4abb-b165-48c036640230

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
open Reformulated.AutPerF.Tilt
variable [IsDomain R]
variable [ValuationRing R]
namespace Reformulated.AutPerF.Tilt
theorem _root_.solution (x : Tilt p R) : IsUnit x ↔ IsUnit (PreTilt.untilt x) := by
  rw [isUnit_iff_dvd_one, isUnit_iff_dvd_one, dvd_iff_untilt_dvd, map_one]
end Reformulated.AutPerF.Tilt

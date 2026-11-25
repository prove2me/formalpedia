-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.isUnit_iff_isUnit_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:40.198828+00:00
-- url     : https://prove2.me/submissions/54cd3ae2-3800-4c0a-9a95-bf795e0a63b7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Tilt_isUnit_iff_isUnit_coeff
import Theorems.Thm_Reformulated_AutPerF_Tilt_isUnit_iff_isUnit_untilt

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
theorem _root_.solution (x : Tilt p R) : IsUnit x ↔ IsUnit (PreTilt.coeff 0 x) := by
  rw [isUnit_iff_isUnit_untilt, ← PreTilt.mk_untilt_eq_coeff_zero, isUnit_iff_isUnit_coeff]
end Reformulated.AutPerF.Tilt

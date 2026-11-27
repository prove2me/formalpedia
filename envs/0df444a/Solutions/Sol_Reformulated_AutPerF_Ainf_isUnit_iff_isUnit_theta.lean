-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.isUnit_iff_isUnit_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:28.825914+00:00
-- url     : https://prove2.me/submissions/25c23757-80db-4081-95eb-9d7f5ffa82cd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Tilt_isUnit_iff_isUnit_coeff
import Theorems.Thm_Reformulated_AutPerF_Tilt_isUnit_iff_isUnit_untilt
import Theorems.Thm_Reformulated_AutPerF_Ainf_isUnit_iff_isUnit_coeff
import Theorems.Thm_Reformulated_AutPerF_Ainf_mk_theta

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
variable [IsDomain R]
variable [ValuationRing R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (x : Ainf p R) : IsUnit x ↔ IsUnit (theta p R x) := by
  rw [isUnit_iff_isUnit_coeff, Tilt.isUnit_iff_isUnit_untilt, ← Tilt.isUnit_iff_isUnit_coeff (p := p),
    ← mk_theta, Tilt.isUnit_iff_isUnit_coeff]
end Reformulated.AutPerF.Ainf

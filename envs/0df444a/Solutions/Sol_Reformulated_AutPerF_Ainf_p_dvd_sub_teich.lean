-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.p_dvd_sub_teich
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:41.103065+00:00
-- url     : https://prove2.me/submissions/53a224a9-757a-4f21-81e1-1bbde2cad4ea

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_p_dvd_iff
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


attribute [local simp] Reformulated.AutPerF.Ainf.theta_xi

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Ainf
omit [IsAdicComplete (span {(p : R)}) R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (x : Ainf p R) : (p : Ainf p R) ∣ x - teich p (x.coeff 0) := by
  rw [p_dvd_iff]
  change WittVector.constantCoeff (x - teich p (x.coeff 0)) = 0
  rw [map_sub]
  simp
end Reformulated.AutPerF.Ainf

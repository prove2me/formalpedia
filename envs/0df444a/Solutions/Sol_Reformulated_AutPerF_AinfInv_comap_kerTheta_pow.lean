-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.comap_kerTheta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:54.958222+00:00
-- url     : https://prove2.me/submissions/93d3180b-dbcc-4aef-aadd-802abf908be0

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_mem_kerTheta_pow_iff
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
open Reformulated.AutPerF.AinfInv
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution (ϖ : PFlat p R) (n : ℕ) :
    (kerTheta p R ^ n).comap (algebraMap (Ainf p R) (AinfInv p R)) = span {Ainf.xi ϖ} ^ n := by
  ext x
  rw [Ideal.mem_comap, algebraMap_mem_kerTheta_pow_iff ϖ, Ideal.span_singleton_pow,
    mem_span_singleton]
end Reformulated.AutPerF.AinfInv

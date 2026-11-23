-- Prove2me | solution 1 for Reformulated.AutPerF.PFlat.twist_div_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:25.767489+00:00
-- url     : https://prove2.me/submissions/f6da7933-a00b-40c0-90f9-6a739b7a8bbf

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
import Theorems.Thm_Reformulated_AutPerF_PFlat_twist_injective
import Theorems.Thm_Reformulated_AutPerF_PFlat_twist_div
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


attribute [local simp] Reformulated.AutPerF.PFlat.twist_div

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Tilt tateModule
open Reformulated.AutPerF.PFlat
variable [IsDomain R] [CharZero R]
variable [ValuationRing R]
namespace Reformulated.AutPerF.PFlat
theorem _root_.solution (η : tateModule p R) (ϖ : PFlat p R) : (ϖ.twist η).div ϖ = η :=
  twist_injective ϖ (twist_div _ _)
end Reformulated.AutPerF.PFlat

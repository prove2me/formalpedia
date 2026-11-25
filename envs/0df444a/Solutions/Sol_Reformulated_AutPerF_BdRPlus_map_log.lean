-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.map_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:07:22.496257+00:00
-- url     : https://prove2.me/submissions/9ec6a524-2067-4abf-a297-46f4b33b8a09

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Theorems.Thm_Reformulated_AutPerF_Acris_eval_log
import Theorems.Thm_Reformulated_AutPerF_Acris_ext_eval
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_map
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_eval_log
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_ext_eval


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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
open Reformulated.AutPerF.BdRPlus
variable {p}
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution (f : R →+* S) (u : BdRPlus p R) (hu : theta p R u = 1) :
    map p f (log u hu) = log (map p f u) (by rw [theta_map, hu, map_one]) := by
  refine ext_eval fun n => ?_
  rw [eval_map, eval_log, eval_log, map_truncLog, ← eval_map, map_sub (map p f), map_one]
end Reformulated.AutPerF.BdRPlus

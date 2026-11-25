-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.iInf_ker_theta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:11:56.50003+00:00
-- url     : https://prove2.me/submissions/e8c9ff31-0d91-442a-ab33-acb9593b3b68

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_eval_eq_zero_of_mem_ker_theta_pow
import Theorems.Thm_Reformulated_AutPerF_Acris_ext_eval
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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.BdRPlus
variable {p}
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution : ⨅ n, fil p R n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_iInf] at hx
  exact ext_eval fun n => by rw [eval_eq_zero_of_mem_ker_theta_pow (hx n), map_zero]
end Reformulated.AutPerF.BdRPlus

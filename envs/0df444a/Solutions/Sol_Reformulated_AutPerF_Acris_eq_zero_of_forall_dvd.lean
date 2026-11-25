-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.eq_zero_of_forall_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:55.268863+00:00
-- url     : https://prove2.me/submissions/5a481fad-f9b5-4e2d-8aae-4a1256ac46af

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Theorems.Thm_Reformulated_AutPerF_Acris_eval_eq_zero_iff
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
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Acris
namespace Reformulated.AutPerF.Acris
theorem _root_.solution {x : Acris p R} (h : ∀ n, (p : Acris p R) ^ n ∣ x) : x = 0 :=
  ext_eval fun n => by rw [(eval_eq_zero_iff n x).2 (h n), map_zero]
end Reformulated.AutPerF.Acris

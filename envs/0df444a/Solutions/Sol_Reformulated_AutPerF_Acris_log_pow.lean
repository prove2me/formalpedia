-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.log_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:11.846385+00:00
-- url     : https://prove2.me/submissions/624a57a5-738e-47bf-9aca-89173d0b2fca

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
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
theorem _root_.solution (u : Ainf p R) (hu : Ainf.theta p R u = 1) (m : ℕ)
    (hm : Ainf.theta p R (u ^ m) = 1) : log (u ^ m) hm = m * log u hu := by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; exact log_one _
  | succ m ih =>
    have h : Ainf.theta p R (u ^ m) = 1 := by rw [map_pow, hu, one_pow]
    rw [log_congr hm (by rw [map_mul, h, hu, one_mul]) (pow_succ u m), log_mul _ _ h hu, ih h]
    push_cast
    ring
end Reformulated.AutPerF.Acris

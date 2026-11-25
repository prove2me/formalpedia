-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.eval_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:24.804779+00:00
-- url     : https://prove2.me/submissions/306bdc1e-212b-4f3a-a432-41d65d0f1b30

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Theorems.Thm_P2M_Reformulated_AutPerF_eval__eq_zero_iff_dvd_74ed1f8e0248

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
theorem _root_.solution (n : ℕ) (x : Acris p R) : eval p R n x = 0 ↔ (p : Acris p R) ^ n ∣ x := by
  have := evalₐ_eq_zero_iff_dvd (p : AcrisZero p R) n x
  rw [map_natCast] at this
  exact this
end Reformulated.AutPerF.Acris

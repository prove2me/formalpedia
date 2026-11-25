-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.exists_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:27.18102+00:00
-- url     : https://prove2.me/submissions/2c5052cb-9f33-4464-8abb-b5433a932860

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Theorems.Thm_Reformulated_AutPerF_Acris_eval_eq_zero_iff

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
theorem _root_.solution (n : ℕ) (x : Acris p R) :
    ∃ (a : AcrisZero p R) (y : Acris p R), x = algebraMap _ _ a + (p : Acris p R) ^ n * y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R n x)
  obtain ⟨y, hy⟩ := (eval_eq_zero_iff n (x - algebraMap _ _ a)).1
    (by rw [map_sub, eval_algebraMap, ha, sub_self])
  exact ⟨a, y, by rw [← hy]; ring⟩
end Reformulated.AutPerF.Acris

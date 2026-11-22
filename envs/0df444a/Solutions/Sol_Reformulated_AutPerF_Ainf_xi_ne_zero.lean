-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.xi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:27.026097+00:00
-- url     : https://prove2.me/submissions/052d2948-7e43-4c2d-a8f2-7f4582763219

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_coeff_zero_xi

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
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution [CharZero R] (ϖ : PFlat p R) : xi ϖ ≠ 0 := by
  intro h
  have h1 := coeff_zero_xi ϖ
  rw [h, WittVector.zero_coeff, eq_comm, neg_eq_zero] at h1
  have h2 := ϖ.2
  rw [h1, Tilt.untilt_zero, eq_comm, Nat.cast_eq_zero] at h2
  exact (Fact.out : p.Prime).ne_zero h2
end Reformulated.AutPerF.Ainf

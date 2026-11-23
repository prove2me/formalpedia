-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.omega_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:06.851123+00:00
-- url     : https://prove2.me/submissions/c29b502c-9b89-407a-94f8-2f5f8e0e47a2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_tateRoot_pow

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
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (ε : tateModule p R) :
    omega ε * (teich p (tateRoot ε) - 1) = teich p ε.1 - 1 := by
  rw [omega, geom_sum_mul, ← map_pow, tateRoot_pow]
end Reformulated.AutPerF.Ainf

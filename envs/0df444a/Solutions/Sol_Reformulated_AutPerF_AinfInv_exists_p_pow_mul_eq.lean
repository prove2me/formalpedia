-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.exists_p_pow_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:07:38.788636+00:00
-- url     : https://prove2.me/submissions/5b283baf-d39f-4d04-896d-bd98d5f83c80

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel

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
open Reformulated.AutPerF.AinfInv
omit [IsAdicComplete (span {(p : R)}) R]
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution (x : AinfInv p R) :
    ∃ (k : ℕ) (a : Ainf p R), (p : AinfInv p R) ^ k * x = algebraMap _ _ a := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (p : Ainf p R) x
  exact ⟨k, a, by rw [← h, map_natCast, mul_comm]⟩
end Reformulated.AutPerF.AinfInv

-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.algebraMap_mem_kerTheta_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:37:37.664029+00:00
-- url     : https://prove2.me/submissions/5352b961-581e-420d-803e-75ae1c7eee4d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_xi_pow_dvd_of_dvd_p_pow_mul
import Theorems.Thm_Reformulated_AutPerF_AinfInv_exists_p_pow_mul_eq
import Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_injective
import Theorems.Thm_Reformulated_AutPerF_AinfInv_kerTheta_eq

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
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution (ϖ : PFlat p R) (n : ℕ) (x : Ainf p R) :
    algebraMap (Ainf p R) (AinfInv p R) x ∈ kerTheta p R ^ n ↔ Ainf.xi ϖ ^ n ∣ x := by
  rw [kerTheta_eq ϖ, Ideal.span_singleton_pow, mem_span_singleton, ← map_pow]
  refine ⟨fun ⟨y, hy⟩ => ?_, fun h => map_dvd _ h⟩
  obtain ⟨k, a, h⟩ := exists_p_pow_mul_eq y
  refine Ainf.xi_pow_dvd_of_dvd_p_pow_mul ϖ (k := k) ⟨a, algebraMap_injective ?_⟩
  rw [map_mul, map_mul, hy, ← h, map_pow (algebraMap (Ainf p R) (AinfInv p R)) (p : Ainf p R),
    map_natCast]
  ring
end Reformulated.AutPerF.AinfInv

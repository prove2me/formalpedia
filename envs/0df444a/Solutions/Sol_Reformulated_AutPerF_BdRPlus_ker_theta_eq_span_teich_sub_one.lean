-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.ker_theta_eq_span_teich_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:33.542161+00:00
-- url     : https://prove2.me/submissions/99ded70e-517c-4e52-a12f-21bf7957ba60

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
import Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_away_injective
import Theorems.Thm_Reformulated_AutPerF_Ainf_exists_teich_sub_one_eq
import Theorems.Thm_Reformulated_AutPerF_Ainf_ker_theta


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
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdRPlus
variable [IsAlgClosed (FractionRing R)]
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution {ε : tateModule p R} (hε : IsPrimitive ε) :
    RingHom.ker (theta p R) = span {algebraMap (Ainf p R) (BdRPlus p R) (Ainf.teich p ε.1 - 1)} := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  obtain ⟨b, hb, hb0⟩ := Ainf.exists_teich_sub_one_eq ϖ hε
  have hu : IsUnit (algebraMap (Ainf p R) (BdRPlus p R) b) := by
    rw [isUnit_iff_theta_ne_zero, theta_algebraMap_ainf]
    exact (map_ne_zero_iff _ AinfInv.algebraMap_away_injective).2 hb0
  rw [ker_theta ϖ, hb, map_mul, Ideal.span_singleton_mul_right_unit hu]
  rfl
end Reformulated.AutPerF.BdRPlus

-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.exists_eq_xi_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:40:21.549511+00:00
-- url     : https://prove2.me/submissions/7df50d9c-3cd3-4d84-b343-d2d8e1552381

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_p_dvd_sub_teich
import Theorems.Thm_Reformulated_AutPerF_Ainf_mk_theta

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
variable [ValuationRing R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (ϖ : PFlat p R) {x : Ainf p R} (hx : (p : R) ∣ theta p R x) :
    ∃ a y, x = xi ϖ * a + p * y := by
  rw [← mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, mk_theta,
    Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := (Tilt.dvd_iff_untilt_dvd ϖ.1 (x.coeff 0)).2 (by rw [ϖ.2]; exact hx)
  obtain ⟨d, hd⟩ := p_dvd_sub_teich x
  rw [hc, map_mul] at hd
  exact ⟨-teich p c, d + teich p c, by rw [xi]; linear_combination hd⟩
end Reformulated.AutPerF.Ainf

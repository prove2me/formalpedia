-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.isUnit_iff_isUnit_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:59.607791+00:00
-- url     : https://prove2.me/submissions/0d6e39c5-cbf3-432b-85f9-3fa224a5376f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_p_dvd_sub_teich

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
omit [IsAdicComplete (span {(p : R)}) R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (x : Ainf p R) : IsUnit x ↔ IsUnit (x.coeff 0) := by
  refine ⟨fun h => h.map WittVector.constantCoeff, fun h => ?_⟩
  obtain ⟨c, hc⟩ := p_dvd_sub_teich x
  obtain ⟨t, ht⟩ := h.map (teich p)
  have hj := IsAdicComplete.le_jacobson_bot (span {(p : Ainf p R)})
    (mem_span_singleton_self (p : Ainf p R))
  have := Ideal.mem_jacobson_bot.1 hj (c * ↑t⁻¹)
  have e : x = ((p : Ainf p R) * (c * ↑t⁻¹) + 1) * t := by
    rw [add_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, one_mul, ← hc, ht, sub_add_cancel]
  rw [e]
  exact this.mul t.isUnit
end Reformulated.AutPerF.Ainf

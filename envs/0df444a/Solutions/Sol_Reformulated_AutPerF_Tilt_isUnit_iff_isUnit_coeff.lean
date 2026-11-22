-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.isUnit_iff_isUnit_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:16.956041+00:00
-- url     : https://prove2.me/submissions/87e0431e-c83c-44cb-9c51-b03299978e02

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
open Reformulated.AutPerF.Tilt
namespace Reformulated.AutPerF.Tilt
theorem _root_.solution [IsLocalRing R] (a : R) :
    IsUnit (Ideal.Quotient.mk (span {(p : R)}) a) ↔ IsUnit a := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), eq_comm, Ideal.Quotient.eq,
    mem_span_singleton] at hb
  obtain ⟨c, hc⟩ := hb
  by_contra ha
  have h1 : a * b ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_right _ _ ha
  have h2 : (p : R) * c ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right _ _ (Fact.out : ¬IsUnit (p : R))
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [show (1 : R) = a * b + p * c by linear_combination hc]; exact add_mem h1 h2
  exact this isUnit_one
end Reformulated.AutPerF.Tilt

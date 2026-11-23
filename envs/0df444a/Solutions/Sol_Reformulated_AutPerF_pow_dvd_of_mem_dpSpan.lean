-- Prove2me | solution 1 for Reformulated.AutPerF.pow_dvd_of_mem_dpSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:44.132351+00:00
-- url     : https://prove2.me/submissions/f65d830d-459c-4eab-b150-a835f11098cf

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
import Theorems.Thm_Reformulated_AutPerF_pow_dvd_dp

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
variable {B : Type*} [CommRing B] [Algebra ℚ B]
variable {A : Type*} [CommRing A] [Algebra A B]
variable {ξ : A}
namespace Reformulated.AutPerF
theorem _root_.solution {s : Set ℕ} {n : ℕ} (h : ∀ m ∈ s, n ≤ m) {x : B}
    (hx : x ∈ dpSpan B ξ s) : algebraMap A B ξ ^ n ∣ x := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨m, hm, rfl⟩ := hx; exact pow_dvd_dp (h m hm) _
  | zero => exact dvd_zero _
  | add x y _ _ hx hy => exact dvd_add hx hy
  | smul a x _ hx => rw [Algebra.smul_def]; exact hx.mul_left _
end Reformulated.AutPerF

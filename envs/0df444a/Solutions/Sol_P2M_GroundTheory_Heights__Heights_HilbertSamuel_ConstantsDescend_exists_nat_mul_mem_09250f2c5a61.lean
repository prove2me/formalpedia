-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_nat_mul_mem_09250f2c5a61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:45.580132+00:00
-- url     : https://prove2.me/submissions/86f48278-1a4e-4502-86e6-6d11dc92b30c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
theorem _root_.solution {Ω : Type*} [Field Ω] [CharZero Ω] (R : Subalgebra ℤ Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (R : Set Ω)) : ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ R := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_pos, ?_⟩
    have : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [eq_ratCast, ← Rat.cast_natCast, ← Rat.cast_mul, mul_comm, Rat.mul_den_eq_num, Rat.cast_intCast]
    rw [this]
    exact Subalgebra.intCast_mem R _
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (x + y) = (n₂ : Ω) * ((n₁ : Ω) * x) + (n₁ : Ω) * ((n₂ : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact R.add_mem (R.mul_mem (Subalgebra.natCast_mem R _) hx) (R.mul_mem (Subalgebra.natCast_mem R _) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (x * y) = ((n₁ : Ω) * x) * ((n₂ : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact R.mul_mem hx hy
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend

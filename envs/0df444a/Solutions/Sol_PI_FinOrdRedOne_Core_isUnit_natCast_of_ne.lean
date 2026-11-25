-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.isUnit_natCast_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:04.124145+00:00
-- url     : https://prove2.me/submissions/02caf644-0f79-46d4-a10c-b312f1e5d1f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.FinOrdRedOne.Core
theorem _root_.solution [IsLocalRing R] (p : ℕ) (hp : p.Prime)
    (hpM : (p : R) ∈ IsLocalRing.maximalIdeal R) (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) :
    IsUnit (l : R) := by
  by_contra h
  have hlM : (l : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h
  have hcop : IsCoprime (l : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl hp).mpr hlp)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : ((u : R) * l + (v : R) * p) = 1 := by
    have := congrArg (Int.cast : ℤ → R) huv
    push_cast at this
    exact this
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlM) (Ideal.mul_mem_left _ _ hpM)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)
end PI.FinOrdRedOne.Core

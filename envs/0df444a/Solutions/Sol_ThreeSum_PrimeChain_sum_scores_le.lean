-- Prove2me | solution 1 for ThreeSum.PrimeChain.sum_scores_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:52:07.648833+00:00
-- url     : https://prove2.me/submissions/6cb2ad95-7d2e-418a-9a80-00b4adca9b37

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-! # Exact deterministic contraction of the weighted modular score -/

namespace ThreeSum.PrimeChain

open Finset
open scoped BigOperators

variable {ι : Type*}































theorem sum_scores (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (C : Finset ℕ) (q : ℕ) :
    (∑ p ∈ C, score T difference weight (q * p)) =
      ∑ i ∈ T, (C.filter fun p => q * p ∣ (difference i).natAbs).card *
        weight (difference i) := by
  unfold score
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter]
  simp

/-- The finite averaging estimate is valid on YES instances too: zero
differences are removed by their zero weight. -/
theorem sum_scores_le_sourceProof (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (hzero : weight 0 = 0) (C : Finset ℕ) (q K : ℕ)
    (hdivisors : ∀ i ∈ T, difference i ≠ 0 →
      (C.filter fun p => p ∣ (difference i).natAbs).card ≤ K) :
    (∑ p ∈ C, score T difference weight (q * p)) ≤ K * score T difference weight q := by
  rw [sum_scores, score, mul_sum]
  apply sum_le_sum
  intro i hi
  by_cases hz : difference i = 0
  · simp [hz, hzero]
  by_cases hq : q ∣ (difference i).natAbs
  · rw [if_pos hq]
    apply Nat.mul_le_mul_right
    apply le_trans (card_le_card ?_) (hdivisors i hi hz)
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,
      dvd_trans (dvd_mul_left p q) (mem_filter.mp hp).2⟩
  · rw [if_neg hq, mul_zero]
    have hempty : (C.filter fun p => q * p ∣ (difference i).natAbs) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hq (dvd_trans (dvd_mul_right q p) (mem_filter.mp hp).2)
    simp [hempty]


































































































end ThreeSum.PrimeChain

end

universe u_1

theorem solution : ∀ {ι : Type u_1} (T : Finset.{u_1} ι) (difference : ι → Int) (weight : Int → Nat),
  @Eq.{1} Nat (weight (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∀ (C : Finset.{0} Nat) (q K : Nat),
      (∀ (i : ι),
          @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
              (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) T i →
            @Ne.{1} Int (difference i) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
              @LE.le.{0} Nat instLENat
                (@Finset.card.{0} Nat ({p ∈ C | @Dvd.dvd.{0} Nat Nat.instDvd p (difference i).natAbs})) K) →
        @LE.le.{0} Nat instLENat
          (∑ p ∈ C,
            @ThreeSum.PrimeChain.score.{u_1} ι T difference weight
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q p))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K
            (@ThreeSum.PrimeChain.score.{u_1} ι T difference weight q)) := by
  exact @ThreeSum.PrimeChain.sum_scores_le_sourceProof

#print axioms solution

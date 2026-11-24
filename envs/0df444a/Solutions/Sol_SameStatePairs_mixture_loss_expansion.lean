-- Prove2me | solution 1 for SameStatePairs.mixture_loss_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:39:30.560882+00:00
-- url     : https://prove2.me/submissions/9ae69b12-4e47-4163-ac38-425c335747e6

import Mathlib
import Definitions.Def_SameStatePairs_Basic

set_option autoImplicit false

open Matrix

open SameStatePairs

/-- General expansion of the pair loss through the row and column sums of `π`. -/
private lemma pairLoss_expand {α : Type*} [Fintype α] {k : ℕ} (π : α → α → ℝ)
    (h : α → Fin k → ℝ) :
    pairLoss π h = ∑ i, (∑ a, (∑ a', π a a') * (h a i * h a i) +
      ∑ a', (∑ a, π a a') * (h a' i * h a' i) -
      2 * ∑ a, ∑ a', π a a' * h a i * h a' i) := by
  have e1 : pairLoss π h = ∑ i, ∑ a, ∑ a', π a a' * (h a i - h a' i) ^ 2 := by
    simp only [pairLoss, sqNorm, Pi.sub_apply, Finset.mul_sum]
    exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
  rw [e1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e2 : ∀ a a', π a a' * (h a i - h a' i) ^ 2 =
      π a a' * (h a i * h a i) + π a a' * (h a' i * h a' i) - 2 * (π a a' * h a i * h a' i) := by
    intro a a'; ring
  simp only [e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 2
  rw [Finset.sum_comm]

theorem solution {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq X] {k : ℕ}
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (κ : Z → X → ℝ) (hκ : IsChannel κ) (hX : ∀ x, 0 < obsLaw p κ x)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (f : X → Fin k → ℝ) (hfc : IsCentered (obsLaw p κ) f) (hfw : IsWhitened (obsLaw p κ) f) :
    pairLoss (mixPairLaw p κ ε) f = 2 * k - 2 * ε * topQuad p κ f := by
  have hsumX : ∑ x, obsLaw p κ x = 1 := by
    simp only [obsLaw]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hκ.2, mul_one, hp1]
  have hrowS : ∀ x, ∑ x', sameStatePairLaw p κ x x' = obsLaw p κ x := by
    intro x
    simp only [sameStatePairLaw, obsLaw]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hκ.2, mul_one]
  have hsymS : ∀ x x', sameStatePairLaw p κ x x' = sameStatePairLaw p κ x' x := by
    intro x x'
    simp only [sameStatePairLaw]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hrow : ∀ x, ∑ x', mixPairLaw p κ ε x x' = obsLaw p κ x := by
    intro x
    simp only [mixPairLaw, Finset.sum_add_distrib, ← Finset.mul_sum, hrowS, hsumX]
    ring
  have hcol : ∀ x', ∑ x, mixPairLaw p κ ε x x' = obsLaw p κ x' := by
    intro x'
    rw [← hrow x']
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [mixPairLaw, hsymS x x']
    ring
  have hnorm : ∀ i, ∑ a, obsLaw p κ a * (f a i * f a i) = 1 := by
    intro i
    have := hfw i i
    simp only [if_true] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hcross : ∀ i, ∑ a, ∑ a', mixPairLaw p κ ε a a' * f a i * f a' i =
      ε * ∑ a, ∑ a', sameStatePairLaw p κ a a' * f a i * f a' i := by
    intro i
    have hc : ∑ a, obsLaw p κ a * f a i = 0 := hfc i
    have : ∀ a a', mixPairLaw p κ ε a a' * f a i * f a' i =
        ε * (sameStatePairLaw p κ a a' * f a i * f a' i) +
          (1 - ε) * ((obsLaw p κ a * f a i) * (obsLaw p κ a' * f a' i)) := by
      intro a a'; simp only [mixPairLaw]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hc]
    ring
  have htop : topQuad p κ f = ∑ i, ∑ a, ∑ a', sameStatePairLaw p κ a a' * f a i * f a' i := by
    simp only [topQuad, sameStateOp, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun a' _ => ?_
    have := (hX a).ne'
    field_simp
  rw [pairLoss_expand]
  simp only [hrow, hcol, hnorm, hcross, htop]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

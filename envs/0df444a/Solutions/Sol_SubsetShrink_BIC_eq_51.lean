-- Prove2me | solution 1 for SubsetShrink.BIC.eq_51
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T17:55:09.063794+00:00
-- url     : https://prove2.me/submissions/7603b522-5cfc-4d31-af56-1ca96f9639d5

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model

open SubsetShrink.BIC

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (a b : ℝ)
    (βhat : Fin p → ℝ) (hβhat : IsBIC2 X (fstar + ε) a b βhat) (β : Fin p → ℝ) :
    ∑ i, (fstar i - X.mulVec βhat i) ^ 2 + lamB a βhat * SubsetShrink.Events.l2 βhat + muB b βhat * (SubsetShrink.Events.l0 βhat : ℝ) ≤
      ∑ i, (fstar i - X.mulVec β i) ^ 2 + 2 * SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) +
        lamB a β * SubsetShrink.Events.l2 β + muB b β * (SubsetShrink.Events.l0 β : ℝ) := by
  -- Expanding the residual `‖(f*+ε) − Xβ‖²` around `‖f* − Xβ‖²`.
  have key : ∀ β : Fin p → ℝ,
      (∑ i, ((fstar + ε) i - X.mulVec β i) ^ 2)
        = (∑ i, (fstar i - X.mulVec β i) ^ 2)
          + 2 * SubsetShrink.Events.dot ε (fun i => fstar i - X.mulVec β i)
          + ∑ i, ε i ^ 2 := by
    intro β
    rw [SubsetShrink.Events.dot, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply]
    ring
  have hdot_lin : ∀ (v : Fin p → ℝ),
      SubsetShrink.Events.dot ε (fun i => fstar i - X.mulVec v i)
        = SubsetShrink.Events.dot ε fstar - SubsetShrink.Events.dot ε (X.mulVec v) := by
    intro v
    rw [SubsetShrink.Events.dot, SubsetShrink.Events.dot, SubsetShrink.Events.dot,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdot_sub :
      SubsetShrink.Events.dot ε (X.mulVec (βhat - β))
        = SubsetShrink.Events.dot ε (X.mulVec βhat) - SubsetShrink.Events.dot ε (X.mulVec β) := by
    rw [SubsetShrink.Events.dot, SubsetShrink.Events.dot, SubsetShrink.Events.dot,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mulVec_sub, Pi.sub_apply]
    ring
  have hmin := hβhat β
  simp only [obj2] at hmin
  rw [key βhat, key β] at hmin
  have e1 := hdot_lin βhat
  have e2 := hdot_lin β
  linarith [hmin, e1, e2, hdot_sub]

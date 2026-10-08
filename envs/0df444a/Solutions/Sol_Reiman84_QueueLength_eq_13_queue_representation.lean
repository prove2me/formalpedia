-- Prove2me | solution 1 for Reiman84.QueueLength.eq_13_queue_representation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:56:59.963548+00:00
-- url     : https://prove2.me/submissions/49f860fe-c4f2-43bc-9ed7-0451aca641af

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Network

set_option autoImplicit false

open MeasureTheory in
theorem solution {K : ℕ} {J : Finset (Fin K)} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (N : Reiman84.QueueLength.Network K J P) (ω : Ω)
    (Q B : ℝ → Fin K → ℝ) (h : N.IsQueueSolution ω Q B) :
    ∀ t, 0 ≤ t → Q t = N.Xtilde B t ω + Matrix.vecMul (N.Y B t) (1 - N.routing) := by
  intro t ht
  have h3 := h.2.2.2.2 t ht
  rw [h3, show (1 - N.routing) = -(N.routing - 1) from (neg_sub _ _).symm]
  funext j
  simp only [Reiman84.QueueLength.Network.Xtilde, Reiman84.QueueLength.Network.Atilde,
    Reiman84.QueueLength.Network.Stilde, Reiman84.QueueLength.Network.eta]
  generalize N.routing - 1 = M
  simp only [Matrix.vecMul, dotProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Matrix.neg_apply, Finset.sum_apply, smul_eq_mul, mul_neg, Finset.sum_neg_distrib]
  have h1 : ∑ c, (N.Shat c (B t c) ω j - N.mu c * B t c * M c j)
      = ∑ c, N.Shat c (B t c) ω j - ∑ c, N.mu c * B t c * M c j := Finset.sum_sub_distrib ..
  have h2 : ∑ i, N.Y B t i * M i j
      = t * ∑ i, N.mu i * M i j - ∑ i, N.mu i * B t i * M i j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by
      show N.mu i * (t - B t i) * M i j = t * (N.mu i * M i j) - N.mu i * B t i * M i j
      ring)
  linarith [h1, h2]

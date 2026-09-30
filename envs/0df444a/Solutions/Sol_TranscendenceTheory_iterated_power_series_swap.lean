-- Prove2me | solution 1 for TranscendenceTheory.iterated_power_series_swap
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T21:36:34.108447+00:00
-- url     : https://prove2.me/submissions/3ac5b204-9faa-4541-8056-56345d160199

import Mathlib.RingTheory.PowerSeries.Basic

open PowerSeries

private lemma transpose_mul {R : Type*} [Semiring R]
    (f g : PowerSeries (PowerSeries R)) :
    (mk fun k => mk fun i => coeff k (coeff i (f * g))) =
      (mk fun k => mk fun i => coeff k (coeff i f)) *
        (mk fun k => mk fun i => coeff k (coeff i g)) := by
  ext k i
  simp only [coeff_mk, coeff_mul, map_sum]
  rw [Finset.sum_comm]

theorem solution
    (R : Type*) [Semiring R] :
    ∃! τ : PowerSeries (PowerSeries R) ≃+* PowerSeries (PowerSeries R),
      ∀ (f : PowerSeries (PowerSeries R)) (i k : ℕ),
        PowerSeries.coeff i (PowerSeries.coeff k (τ f)) =
          PowerSeries.coeff k (PowerSeries.coeff i f) := by
  let swap : PowerSeries (PowerSeries R) → PowerSeries (PowerSeries R) :=
    fun f => mk fun k => mk fun i => coeff k (coeff i f)
  have hinv (f : PowerSeries (PowerSeries R)) : swap (swap f) = f := by
    ext k i
    simp [swap]
  let τ : PowerSeries (PowerSeries R) ≃+* PowerSeries (PowerSeries R) :=
    { toFun := swap
      invFun := swap
      left_inv := hinv
      right_inv := hinv
      map_add' := by intro f g; ext k i; simp [swap]
      map_mul' := transpose_mul }
  refine ⟨τ, ?_, ?_⟩
  · intro f i k
    simp [τ, swap]
  · intro σ hσ
    apply RingEquiv.ext
    intro f
    ext k i
    rw [hσ f i k]
    simp [τ, swap]

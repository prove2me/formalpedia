-- Prove2me | solution 1 for RobustMultiStop.c5_c6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:55:53.131768+00:00
-- url     : https://prove2.me/submissions/92d6b2da-e861-41e2-aa47-277c35b1bb4d

import Mathlib
import Definitions.Def_RobustMultiStop_IsDMU

open MeasureTheory

open RobustMultiStop in
theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ)) (hρ : IsDMU F N 𝔛 ρ) :
    ∀ t ≤ N, ρ t 0 = 0 ∧
      ∀ X ∈ 𝔛, AEStronglyMeasurable[F t] (X : Ω → ℝ) P → ρ t X = X := by
  intro t ht
  have hZ : ((0 : Ω →ₘ[P] ℝ) : Ω → ℝ) =ᵐ[P] (∅ : Set Ω).indicator ((0 : Ω →ₘ[P] ℝ) : Ω → ℝ) :=
    AEEqFun.coeFn_zero.trans (by rw [Set.indicator_empty]; first | done | exact Filter.EventuallyEq.rfl)
  obtain ⟨-, h⟩ := hρ.regular t ht ∅ (@MeasurableSet.empty Ω (F t)) 0 (Submodule.zero_mem 𝔛) 0 hZ
  have h0 : ρ t 0 = 0 :=
    AEEqFun.ext (h.trans (by
      rw [Set.indicator_empty]
      first | done | exact AEEqFun.coeFn_zero.symm))
  refine ⟨h0, fun X hX hXm => ?_⟩
  have := hρ.transl t ht 0 (Submodule.zero_mem 𝔛) X hX hXm
  rw [zero_add, h0, zero_add] at this
  exact this

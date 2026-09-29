-- Prove2me | solution 1 for StochasticOrders.Usual.hazard_rate_order_imp_usual_order
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T02:49:32.503142+00:00
-- url     : https://prove2.me/submissions/92d6d2b1-afce-4824-a6df-6ed197d22c08

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Definitions.Def_StochasticOrders_Usual_HazardRateOrder

/-! Disproof of 2f8ec3a3 `StochasticOrders.Usual.hazard_rate_order_imp_usual_order`.

The statement puts no probability assumption on `μ`, `ν`. Take `Ω = Ω' = Unit`,
`μ = dirac ()`, `ν = 0`, `X = Y ≡ 0`. Every survival value of `Y` is `0`, so both sides of
the hazard-rate inequality `F̄(y) Ḡ(x) ≤ F̄(x) Ḡ(y)` are `0` and `X ≤hr Y` holds. But
`μ {-1 < X} = 1 > 0 = ν {-1 < Y}`, so `X ≤st Y` fails. -/

set_option autoImplicit false

open MeasureTheory StochasticOrders.Usual in
theorem solution : ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) (h : HazardRateOrder μ ν X Y),
    UsualOrder μ ν X Y) := by
  intro H
  have h : HazardRateOrder (Measure.dirac ()) (0 : Measure Unit) (fun _ => (0:ℝ))
      (fun _ => (0:ℝ)) := by
    intro x y _
    simp [survival]
  have key := H _ _ _ _ h (-1)
  have e : {ω : Unit | (-1:ℝ) < (fun _ => (0:ℝ)) ω} = Set.univ := by
    ext ω
    simp
  rw [e, measure_univ, Measure.coe_zero, Pi.zero_apply] at key
  exact absurd key (by simp)

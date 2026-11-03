-- Prove2me | solution 1 for RiskStopTC.recursive_property
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:06:59.746507+00:00
-- url     : https://prove2.me/submissions/fe3fe9d4-359a-4024-a60d-c345e4cfa8dd

import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_RiskStopTC_nested
import Lean.Elab.Tactic.Omega
open MeasureTheory RiskFunctionals.NestedAVaR RiskStopTC
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (s t u : ℕ) (hst : s ≤ t) (htu : t ≤ u) (huT : u ≤ T)
    (X : Ω → ℝ) :
    nested ϱ s u X = nested ϱ s t (nested ϱ t u X) := by
  induction h : t - s using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hs : s < t
    · have hsu : s < u := lt_of_lt_of_le hs htu
      rw [RiskStopTC.nested, if_pos hsu]
      conv_rhs => rw [RiskStopTC.nested, if_pos hs]
      apply congrArg (ϱ s)
      exact ih (t - (s + 1)) (by omega) (s + 1) (by omega) rfl
    · have hst' : s = t := Nat.le_antisymm hst (Nat.le_of_not_gt hs)
      subst s
      conv_rhs => rw [RiskStopTC.nested, if_neg (Nat.lt_irrefl t)]
#print axioms solution

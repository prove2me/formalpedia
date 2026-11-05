-- Prove2me | solution 1 for ProbabilityTheory.poissonTimeCount_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:05:50.390998+00:00
-- url     : https://prove2.me/submissions/fd34fea2-83c2-4405-95ff-9aa70e581733

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω E : Type} [MeasurableSpace E]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × E} {A : Set E}
  {s t : ℝ}

theorem solution (hA : MeasurableSet A) (h0s : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    poissonTimeCount K X A t ω
      = poissonTimeCount K X A s ω + poissonRandomMeasure K X ω (Set.Ioc s t ×ˢ A) := by
  unfold poissonTimeCount
  rw [← Set.Ioc_union_Ioc_eq_Ioc h0s hst, Set.union_prod,
    measure_union (Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le le_rfl) A A)
      (measurableSet_Ioc.prod hA)]

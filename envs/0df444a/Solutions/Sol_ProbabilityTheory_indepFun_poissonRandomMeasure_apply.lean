-- Prove2me | solution 1 for ProbabilityTheory.indepFun_poissonRandomMeasure_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:33:40.749501+00:00
-- url     : https://prove2.me/submissions/b73b2382-b741-4d7e-8720-9ee219427676

import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.FinCases
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_apply

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-! Original LeanLevy two-set independence follows from its proved mutual independence theorem. -/
theorem solution
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {A B : Set E}
    [IsProbabilityMeasure μ]
    (hd : ProbabilityTheory.IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) :
    IndepFun (fun ω => ProbabilityTheory.poissonRandomMeasure K X ω A)
      (fun ω => ProbabilityTheory.poissonRandomMeasure K X ω B) μ := by
  let C : Fin 2 → Set E := fun i => if i = 0 then A else B
  have hmeas : ∀ i, MeasurableSet (C i) := by
    intro i
    fin_cases i
    · simpa [C] using hA
    · simpa [C] using hB
  have hfin : ∀ i, m (C i) < ⊤ := by
    intro i
    fin_cases i
    · simpa [C] using hfinA
    · simpa [C] using hfinB
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint (C 0) (C 1)
      simpa [C] using hAB
    · change Disjoint (C 1) (C 0)
      simpa [C] using hAB.symm
    · exact (hij rfl).elim
  have hall := ProbabilityTheory.iIndepFun_poissonRandomMeasure_apply hd hmeas hfin hdisj
  have h01 := hall.indepFun (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  simpa [C] using h01

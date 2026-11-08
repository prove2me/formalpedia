-- Prove2me | solution 1 for ProbabilityTheory.indepFun_poissonRandomMeasure_families
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:40:59.381753+00:00
-- url     : https://prove2.me/submissions/9f9c378a-cc6b-462e-9b8a-ebc64882ff33

import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_families

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
variable {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
variable {m : Measure E} {μ : Measure Ω} [SigmaFinite m] [Nonempty E]

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {ιB ιC : Type} [Fintype ιB] [Fintype ιC]
    {B : ιB → Set E} {C : ιC → Set E}
    (hBm : ∀ i, MeasurableSet (B i)) (hCm : ∀ j, MeasurableSet (C j))
    (hBfin : ∀ i, m (B i) < ⊤) (hCfin : ∀ j, m (C j) < ⊤)
    (hBC : ∀ i j, Disjoint (B i) (C j)) :
    IndepFun (fun ω (i : ιB) => poissonRandomMeasure K X ω (B i))
      (fun ω (j : ιC) => poissonRandomMeasure K X ω (C j)) μ := by
  classical
  -- Package the two families as a `Bool`-indexed family and read off the two-index independence.
  haveI : ∀ b : Bool, Fintype (bif b then ιB else ιC) := by
    rintro (_ | _)
    · exact (inferInstance : Fintype ιC)
    · exact (inferInstance : Fintype ιB)
  have key := iIndepFun_poissonRandomMeasure_families hd
    (ιB := fun b : Bool => bif b then ιB else ιC) (B := Bool.rec C B)
    (fun i => by cases i <;> assumption) (fun i => by cases i <;> assumption)
    (by
      rintro (_ | _) (_ | _) hij b b'
      · exact absurd rfl hij
      · exact (hBC b' b).symm
      · exact hBC b b'
      · exact absurd rfl hij)
  exact key.indepFun (i := true) (j := false) (by decide)


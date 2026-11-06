-- Prove2me | solution 1 for ProbabilityTheory.indep_prmEvalSigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:56:16.400487+00:00
-- url     : https://prove2.me/submissions/35a30baf-7824-4cc8-b16f-a61bbb15f430

import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Theorems.Thm_ProbabilityTheory_iIndep_prmEvalSigma
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ProbabilityTheory MeasureTheory
open scoped ENNReal
variable {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E}
  {μ : Measure Ω} [SigmaFinite m] [Nonempty E]
theorem solution [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {R S : Set E} (hRS : Disjoint R S) :
    Indep (prmEvalSigma K X m R) (prmEvalSigma K X m S) μ := by
  classical
  -- The `Bool`-indexed pair `{R, S}` is pairwise disjoint, so the mutual scattering specializes.
  have hpair : Pairwise (Function.onFun Disjoint (fun b : Bool => bif b then R else S)) := by
    rintro (_ | _) (_ | _) hij
    · exact absurd rfl hij
    · exact hRS.symm
    · exact hRS
    · exact absurd rfl hij
  exact (iIndep_prmEvalSigma hd hpair).indep (i := true) (j := false) (by decide)

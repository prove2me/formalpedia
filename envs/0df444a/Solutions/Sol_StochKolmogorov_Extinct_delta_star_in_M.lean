-- Prove2me | solution 1 for StochKolmogorov.Extinct.delta_star_in_M
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T17:41:49.625323+00:00
-- url     : https://prove2.me/submissions/7adbafed-e98f-41d4-8112-5a2e279eac8e

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_StochKolmogorov_Persist_dirac_mem_M

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ExtinctDirac

/-- The same coefficients, read in the `Persist` copy of the model. -/
def toP {n : ℕ} (C : StochKolmogorov.Extinct.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

open EthierKurtz StochKolmogorov.Extinct in
theorem dirac_mem_ext {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    (Measure.dirac (0 : SDEState n)) ∈ bdryErgodic P X :=
  StochKolmogorov.Persist.dirac_mem_M hn P (toP C) B X hX c γb hA

end ExtinctDirac

open StochKolmogorov.Extinct EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    (Measure.dirac (0 : SDEState n)) ∈ bdryErgodic P X := by
  exact ExtinctDirac.dirac_mem_ext hn P C B X hX c γb hA

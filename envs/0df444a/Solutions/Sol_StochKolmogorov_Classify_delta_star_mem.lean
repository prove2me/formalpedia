-- Prove2me | solution 1 for StochKolmogorov.Classify.delta_star_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T22:32:48.683203+00:00
-- url     : https://prove2.me/submissions/776b991e-bc60-4e69-82c9-36244eedb0ed

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_StochKolmogorov_Persist_dirac_mem_M

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

set_option autoImplicit false

namespace ClassifyDirac

/-- The same coefficients, read in the `Persist` copy of the model. -/
def toP {n : ℕ} (C : StochKolmogorov.Classify.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

open EthierKurtz StochKolmogorov.Classify in
theorem dirac_mem {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    Measure.dirac (0 : SDEState n) ∈ bdryErgodic P X :=
  StochKolmogorov.Persist.dirac_mem_M hn P (toP C) B X hX c γb hA

end ClassifyDirac

open StochKolmogorov.Classify EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    Measure.dirac (0 : SDEState n) ∈ bdryErgodic P X := by
  exact ClassifyDirac.dirac_mem hn P C B X hX c γb hA

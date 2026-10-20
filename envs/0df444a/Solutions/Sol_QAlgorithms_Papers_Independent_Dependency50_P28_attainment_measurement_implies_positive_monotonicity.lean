-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P28.attainment_measurement_implies_positive_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:44:02.101802+00:00
-- url     : https://prove2.me/submissions/05ce4493-1a90-478e-8508-84704e4744f2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.23: AM and measurement monotonicity imply positive-map monotonicity. AM is exact single-shot attainment, not AAM. The output’s attaining measurement is pulled back through the positive TP map; no complete positivity is imposed. -/
theorem solution (d : Divergence) :
    AM d → MMON d → PTPMON d := by
  intro hAM hMM I' J' _ _ _ _ rho sigma hr hs Phi hP hT
  have hd : ∀ X : Mat I', IsDensityMatrix X → IsDensityMatrix (Phi X) :=
    fun X hX => ⟨hP X hX.1, (hT X).trans hX.2⟩
  obtain ⟨M, hM⟩ := hAM J' (Phi rho) (Phi sigma) (hd _ hr) (hd _ hs)
  let M' : CommutingRangeMeasurement I' :=
    { out := M.out
      map := M.map ∘ₗ Phi
      positive := fun A hA => M.positive _ (hP A hA)
      tracePreserving := fun A => (M.tracePreserving _).trans (hT A)
      commuting := fun A B => M.commuting _ _ }
  have h := hMM I' rho sigma hr hs M'
  rw [← hM]
  exact h


end


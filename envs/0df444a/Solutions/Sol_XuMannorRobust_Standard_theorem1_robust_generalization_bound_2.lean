-- Prove2me | solution 2 for XuMannorRobust.Standard.theorem1_robust_generalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:55:51.698652+00:00
-- url     : https://prove2.me/submissions/003761d1-abd6-41df-977d-a42ac51f29c6

import Mathlib
import Definitions.Def_XuMannorRobust_Standard_Losses
import Definitions.Def_XuMannorRobust_Standard_IsRobust
import Definitions.Def_XuMannorRobust_Standard_CellCount
import Theorems.Thm_XuMannorRobust_Standard_eq3_cell_deviation_bound
import Theorems.Thm_XuMannorRobust_Standard_eq4_gap_le_cell_deviation

-- carved verbatim out of submission 9e97ffe3-75d2-4c63-9dd4-b392072fee0b, lines 301-317

noncomputable section
open MeasureTheory ProbabilityTheory XuMannorRobust.Standard
open scoped BigOperators

theorem solution {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ) (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    (hl_meas : ∀ h, Measurable (l h)) {n : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H) (K : ℕ)
    (ε : (Fin n → Z) → ℝ) (hA : IsRobust l A K ε) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => μ)
        {s | ¬ (|expectedLoss μ l (A s) - empiricalLoss l (A s) s|
            ≤ ε s + M * Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))}
      ≤ ENNReal.ofReal δ := by
  obtain ⟨C, hCm, hCd, hCc, hCr⟩ := hA
  apply le_trans (measure_mono ?_) (XuMannorRobust.Standard.eq3_cell_deviation_bound μ C hCm hCd hCc hn δ hδ)
  intro s hs hgood
  apply hs
  have hgap := XuMannorRobust.Standard.eq4_gap_le_cell_deviation μ l M hl_bound hl_meas hn A ε C hCm hCd hCc hCr s
  have hM : 0 ≤ M := (hl_bound (A s) (s ⟨0, hn⟩)).1.trans (hl_bound (A s) (s ⟨0, hn⟩)).2
  have hh := mul_le_mul_of_nonneg_left hgood hM
  linarith

end

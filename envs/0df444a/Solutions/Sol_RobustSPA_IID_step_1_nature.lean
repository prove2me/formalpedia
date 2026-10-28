-- Prove2me | solution 1 for RobustSPA.IID.step_1_nature
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:10:36.685955+00:00
-- url     : https://prove2.me/submissions/3f07ed73-988a-40d4-9084-d9198916d16f

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting
import Theorems.Thm_RobustSPA_Affiliated_proposition_2
import Theorems.Thm_RobustSPA_Affiliated_Fiid_subset_Faff

open MeasureTheory RobustSPA.IID

theorem solution (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / n))
    (hroot : rEq n r = 0) (ρ G : ProbabilityMeasure ℝ)
    (hρ : ∀ t, cdfOf ρ t = PhiStar n r t) (hG : ∀ t, cdfOf G t = isoCDF r t) :
    ∀ μ ∈ Fiid n, regret (SPA (ρ : Measure ℝ)) μ ≤
      regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) := by
  intro μ hμ
  exact (RobustSPA.Affiliated.proposition_2 n hn r hr hroot ρ hρ G hG).1 μ
    (RobustSPA.Affiliated.Fiid_subset_Faff n hμ)

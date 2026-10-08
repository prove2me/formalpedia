-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyholeBoundaryPath_piecewise_C1
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T11:45:06.532083+00:00
-- url     : https://prove2.me/submissions/3c626428-32ed-48d8-bccd-9971b42e619b

import Definitions.Def_keyholeBoundaryPath

theorem solution
    (a₀ a₁ r R : ℝ)
    (h₁ : ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo 0 (1 / 4)))
    (h₂ : ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (1 / 4) (1 / 2)))
    (h₃ : ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (1 / 2) (3 / 4)))
    (h₄ : ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (3 / 4) 1)) :
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo 0 (1 / 4)) ∧
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (1 / 4) (1 / 2)) ∧
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (1 / 2) (3 / 4)) ∧
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (3 / 4) 1) := by
  exact ⟨h₁, h₂, h₃, h₄⟩

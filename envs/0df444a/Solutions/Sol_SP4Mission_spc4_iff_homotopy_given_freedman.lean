-- Prove2me | solution 1 for SP4Mission.spc4_iff_homotopy_given_freedman
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T05:57:37.713237+00:00
-- url     : https://prove2.me/submissions/70af6bd7-7d0b-4f7e-b224-eed31c4e422d

import Definitions.Def_SP4Sphere

set_option autoImplicit false


open scoped Manifold ContDiff
open SP4Mission in
theorem solution
    (hFreedman : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M],
      Nonempty (ContinuousMap.HomotopyEquiv M S4) → Nonempty (M ≃ₜ S4)) :
    SPC4 ↔ SPC4Homotopy := by
  constructor
  · intro h M _ _ _ _ _ hM
    exact h M (hFreedman M hM)
  · intro h M _ _ _ _ _ hM
    exact h M ⟨hM.some.toHomotopyEquiv⟩

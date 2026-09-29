-- Prove2me | solution 1 for VectorSpaceOpt.hahn_banach_norm_preserving
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:47:48.409413+00:00
-- url     : https://prove2.me/submissions/a767387d-7708-437d-993c-f98638cd01f8

import Mathlib


theorem solution {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (f : M →L[ℝ] ℝ) :
    ∃ F : X →L[ℝ] ℝ, (∀ m : M, F m = f m) ∧ ‖F‖ = ‖f‖ := by
  exact exists_extension_norm_eq M f

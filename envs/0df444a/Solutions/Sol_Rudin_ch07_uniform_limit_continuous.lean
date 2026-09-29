-- Prove2me | solution 1 for Rudin.ch07_uniform_limit_continuous
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:39:22.578532+00:00
-- url     : https://prove2.me/submissions/b299e13a-7152-47f4-9564-9dc26373a55d

import Mathlib
set_option autoImplicit false
open Filter Topology
theorem solution {X : Type*} [MetricSpace X] (E : Set X) (f : ℕ → X → ℂ)
    (g : X → ℂ) (hcont : ∀ n, ContinuousOn (f n) E) (huc : TendstoUniformlyOn f g atTop E) :
    ContinuousOn g E := by
  exact huc.continuousOn (Filter.Eventually.of_forall hcont).frequently
#print axioms solution

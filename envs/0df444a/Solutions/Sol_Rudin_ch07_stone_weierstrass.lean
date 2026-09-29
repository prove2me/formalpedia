-- Prove2me | solution 1 for Rudin.ch07_stone_weierstrass
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-13T20:01:26.074452+00:00
-- url     : https://prove2.me/submissions/acb511f9-0e64-449c-9d7e-71b28cd2aad1

import Mathlib
import Definitions.Def_Rudin_ch07_families
set_option autoImplicit false
open Filter Topology Rudin
theorem solution : ¬ (∀ {X : Type} [MetricSpace X],
    ∀ (K : Set X) (hK : IsCompact K)
    (A : Set (X → ℝ)) (halg : IsFunctionAlgebra A) (hcont : ∀ f ∈ A, ContinuousOn f K)
    (hsep : SeparatesPointsOn A K) (hvan : VanishesAtNoPointOn A K),
    ∀ g : X → ℝ, ContinuousOn g K → g ∈ UniformClosureOn A K) := by
  intro h
  have he := h (X := PUnit) (∅ : Set PUnit) isCompact_empty
    (∅ : Set (PUnit → ℝ)) (by simp [IsFunctionAlgebra])
    (by simp) (by simp [SeparatesPointsOn]) (by simp [VanishesAtNoPointOn])
    (fun _ => 0) continuous_const.continuousOn
  obtain ⟨f, hf, _⟩ := he
  exact hf 0
#print axioms solution

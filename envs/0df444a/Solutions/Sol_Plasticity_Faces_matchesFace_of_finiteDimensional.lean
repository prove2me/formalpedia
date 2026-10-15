-- Prove2me | solution 1 for Plasticity.Faces.matchesFace_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:46:03.69048+00:00
-- url     : https://prove2.me/submissions/1dfa8b92-2ba1-4b9a-bba1-3eb899c67c77

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Theorems.Thm_Plasticity_Faces_exists_isCompact_boundary_preimage_subset
import Theorems.Thm_Plasticity_Faces_matchesFace_of_boundary_preimage_relativelyCompact

open Plasticity
open scoped Pointwise

namespace Sol_Plasticity_Faces_matchesFace_of_finiteDimensional

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Strong induction on the dimension: every finite-dimensional sphere face of the unit ball of
`Y` is good for `F`. -/
theorem good (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1)) :
    ∀ n : ℕ, ∀ C : Set Y, IsSphereFace C → FiniteDimensional ℝ (vectorSpan ℝ C) →
      Module.finrank ℝ (vectorSpan ℝ C) = n → MatchesFace F C := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro C hC hfin hn
  have ih : ∀ C' : Set Y, IsSphereFace C' → C' ⊆ C →
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) →
        MatchesFace F C' := by
    intro C' hC' hsub hlt
    have hfin' : FiniteDimensional ℝ (vectorSpan ℝ C') :=
      Submodule.finiteDimensional_of_le (vectorSpan_mono ℝ hsub)
    exact IH _ (hn ▸ hlt) C' hC' hfin' rfl
  exact Plasticity.Faces.matchesFace_of_boundary_preimage_relativelyCompact F hbij hlip C hC hfin ih
    (Plasticity.Faces.exists_isCompact_boundary_preimage_subset F hbij hlip C hC hfin ih)

end Sol_Plasticity_Faces_matchesFace_of_finiteDimensional

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (D : Set X) (hD : D = Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) :
    IsSphereFace D ∧ IsCompact D ∧ FiniteDimensional ℝ (vectorSpan ℝ D) ∧
    Module.finrank ℝ (vectorSpan ℝ D) = Module.finrank ℝ (vectorSpan ℝ C) ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (-C) = -D ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (intrinsicFrontier ℝ C) = intrinsicFrontier ℝ D ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (C.extremePoints ℝ) = D.extremePoints ℝ ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, F '' (t • D) = t • C := by
  subst hD
  exact Sol_Plasticity_Faces_matchesFace_of_finiteDimensional.good F hbij hlip _ C hC hfin rfl

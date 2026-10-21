-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P27.augmentedConstraintDependence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:01:00.655004+00:00
-- url     : https://prove2.me/submissions/bd97bdd1-1c6b-4c2e-8bdf-b34fea05147a

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27
noncomputable section

open QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF pp.4–5, Eqs.(15)–(16): the first stationarity relation makes the
augmented family of constraint differentials linearly dependent. Differentials
are the cotangent version of the displayed Euclidean gradients. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (m : ℕ)
    (f : E → ℝ) (g : Fin m → E → ℝ) (x : E) (lambda : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : ∀ j, DifferentiableAt ℝ (g j) x)
    (hfeasible : ∀ j, g j x = 0)
    (hstation : fderiv ℝ f x = ∑ j, lambda j • fderiv ℝ (g j) x) :
    ¬LinearIndependent ℝ (fun i : Unit ⊕ Fin m =>
      Sum.elim (fun _ : Unit => fderiv ℝ f x) (fun j => fderiv ℝ (g j) x) i) := by
  intro h
  rw [linearIndependent_sum] at h
  obtain ⟨h1, -, h3⟩ := h
  have hne : fderiv ℝ f x ≠ 0 := h1.ne_zero ()
  apply hne
  rw [Submodule.disjoint_def] at h3
  apply h3
  · exact Submodule.subset_span ⟨(), rfl⟩
  · rw [hstation]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))


end

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.groupObjectsInSmoothManifolds
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:35:56.125741+00:00
-- url     : https://prove2.me/submissions/45c886cc-9a02-4382-beae-2b9ac0264441

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
open scoped Manifold ContDiff
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF p. 3, footnote 3: group objects in ordinary differentiable manifolds
are Lie groups. Both sides use the SAME finite-dimensional real smooth manifold
without boundary, with the usual Hausdorff and second countable conventions.
Dimension zero is included. -/
theorem solution
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type u} [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [IsManifold (𝓘(ℝ, E)) ∞ G] (D : GroupMaps G) :
    SmoothGroupObject (E := E) D ↔
      ∃ h : GroupDiagrams D,
        letI : Group G := groupOfMaps D h
        LieGroup (𝓘(ℝ, E)) ∞ G := by
  constructor
  · rintro ⟨h,hm,hi⟩
    refine ⟨h,?_⟩
    letI : Group G := groupOfMaps D h
    exact { contMDiff_mul := hm, contMDiff_inv := hi }
  · rintro ⟨h,hL⟩
    letI : Group G := groupOfMaps D h
    letI : LieGroup (𝓘(ℝ,E)) ∞ G := hL
    exact ⟨h,contMDiff_mul (𝓘(ℝ,E)) ∞,contMDiff_inv (𝓘(ℝ,E)) ∞⟩

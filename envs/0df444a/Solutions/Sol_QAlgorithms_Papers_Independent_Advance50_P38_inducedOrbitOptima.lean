-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.inducedOrbitOptima
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:03:04.479804+00:00
-- url     : https://prove2.me/submissions/90d262c5-e2d7-42e0-89f7-d794f432a4dd

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

theorem solution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G M : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [IsManifold 𝓘(ℝ, E) ∞ G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [T2Space G] [SecondCountableTopology G]
    [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (alpha : M → G → M)
    (hsmooth : ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun p : M × G => alpha p.1 p.2))
    (hone : ∀ x, alpha x 1 = x)
    (hmul : ∀ x g h, alpha (alpha x g) h = alpha x (g * h))
    (quality : M → ℝ) (hquality : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ quality) (x : M) :
    let f : G → ℝ := fun g => quality (alpha x g)
    let fhat : Set.range (alpha x) → ℝ := fun y => quality y.val
    Set.range f = Set.range fhat ∧
    (∀ g, (∀ h, f h ≤ f g) ↔ ∀ y : Set.range (alpha x), fhat y ≤ f g) ∧
    (∀ h g, alpha x h = x → f (h * g) = f g) ∧
    (∀ g h, alpha x g = alpha x h → f g = f h) := by
  intro f fhat
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext r
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨alpha x g, g, rfl⟩, rfl⟩
    · rintro ⟨⟨y, g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  · intro g
    constructor
    · rintro H ⟨y, h, rfl⟩
      exact H h
    · intro H h
      exact H ⟨alpha x h, h, rfl⟩
  · intro h g hh
    show quality (alpha x (h * g)) = quality (alpha x g)
    rw [← hmul, hh]
  · intro g h hgh
    show quality (alpha x g) = quality (alpha x h)
    rw [hgh]

end

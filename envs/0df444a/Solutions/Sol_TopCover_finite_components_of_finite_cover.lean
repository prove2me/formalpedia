-- Prove2me | solution 1 for TopCover.finite_components_of_finite_cover
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T07:29:56.709564+00:00
-- url     : https://prove2.me/submissions/e9e4a056-25bf-41e0-8dbd-793d420d402b

import Mathlib

theorem solution {α : Type*} [TopologicalSpace α] {U : Set α}
    {ι : Type*} [Finite ι] (V : ι → Set α)
    (hconn : ∀ i, IsPreconnected (V i)) (hsub : ∀ i, V i ⊆ U) (hcov : U ⊆ ⋃ i, V i) :
    {C : Set α | ∃ x ∈ U, C = connectedComponentIn U x}.Finite := by
  classical
  set φ : ι → Set α := fun i =>
    if h : (V i).Nonempty then connectedComponentIn U h.choose else ∅ with hφ
  refine Set.Finite.subset (Set.finite_range φ) ?_
  rintro C ⟨x, hxU, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hxU)
  have hVne : (V i).Nonempty := ⟨x, hi⟩
  refine ⟨i, ?_⟩
  simp only [hφ, dif_pos hVne]
  -- `V i` is connected, inside `U`, and meets the component of `x`
  have hsubC : V i ⊆ connectedComponentIn U x :=
    (hconn i).subset_connectedComponentIn hi (hsub i)
  have hmem : hVne.choose ∈ connectedComponentIn U x := hsubC hVne.choose_spec
  exact (connectedComponentIn_eq hmem).symm

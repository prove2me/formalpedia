-- Prove2me | solution 1 for PolygonalArcCarrierCompact
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:01:02.636487+00:00
-- url     : https://prove2.me/submissions/a4e890f3-4657-4493-ac18-bd506c080860

import Definitions.Def_PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCarrierCompact]
theorem solution (γ : PolygonalArc) : IsCompact γ.carrier := by
  rw [γ.carrier_eq]
  let segSet : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
    if h : i + 1 < γ.vertices.length then
      segment ℝ γ.vertices[i] γ.vertices[i + 1]
    else
      ∅
  have h_eq :
      {p | ∃ i : ℕ, ∃ hi : i + 1 < γ.vertices.length,
        p ∈ segment ℝ γ.vertices[i] γ.vertices[i + 1]} =
        ⋃ i ∈ Finset.range γ.vertices.length, segSet i := by
    ext p
    constructor
    · rintro ⟨i, hi, hp⟩
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      refine Set.mem_iUnion.2 ⟨Finset.mem_range.2 (Nat.lt_of_succ_lt hi), ?_⟩
      simp [segSet, hi, hp]
    · intro hp
      rcases Set.mem_iUnion.1 hp with ⟨i, hp⟩
      rcases Set.mem_iUnion.1 hp with ⟨_, hp⟩
      by_cases hi : i + 1 < γ.vertices.length
      · exact ⟨i, hi, by simpa [segSet, hi] using hp⟩
      · simp [segSet, hi] at hp
  rw [h_eq]
  exact Finset.isCompact_biUnion (Finset.range γ.vertices.length) (fun i _ => by
    by_cases hi : i + 1 < γ.vertices.length
    · simp [segSet, hi]
      rw [segment_eq_image]
      exact isCompact_Icc.image (by fun_prop)
    · simp [segSet, hi])

-- Prove2me | solution 1 for PolygonalSideStripsReverseOfSameCarrier
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:40:53.264507+00:00
-- url     : https://prove2.me/submissions/ca4ae324-8504-4c56-b77d-69914070c750

import Mathlib
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonalArc

open Classical in
theorem solution (γ δ : PolygonalArc)
    (S : PolygonalSideStrips γ) :
    δ.carrier = γ.carrier →
      δ.source = γ.target →
        δ.target = γ.source →
          ∃ T : PolygonalSideStrips δ,
            T.leftStrip = S.rightStrip ∧ T.rightStrip = S.leftStrip := by
  intro hc hs ht
  have hri : δ.relativeInterior = γ.relativeInterior := by
    rw [δ.relativeInterior_eq, γ.relativeInterior_eq, hc, hs, ht, Set.pair_comm]
  exact ⟨{ collar := S.collar
           leftStrip := S.rightStrip
           rightStrip := S.leftStrip
           collar_open := S.collar_open
           left_open := S.right_open
           right_open := S.left_open
           relativeInterior_subset_collar := hri ▸ S.relativeInterior_subset_collar
           left_subset_collar := S.right_subset_collar
           right_subset_collar := S.left_subset_collar
           left_connected := S.right_connected
           right_connected := S.left_connected
           left_disjoint_arc := hc ▸ S.right_disjoint_arc
           right_disjoint_arc := hc ▸ S.left_disjoint_arc
           side_strips_disjoint := S.side_strips_disjoint.symm
           relativeInterior_subset_closure_left := hri ▸ S.relativeInterior_subset_closure_right
           relativeInterior_subset_closure_right := hri ▸ S.relativeInterior_subset_closure_left
           collar_without_arc := by rw [hri, S.collar_without_arc, Set.union_comm] }, rfl, rfl⟩

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.boolean_finite_type_iff_frame_law
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:22:22.437091+00:00
-- url     : https://prove2.me/submissions/5d3d186a-bf4f-47d1-8158-1e5e8dcdd196

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_frame_stone_extremally_disconnected
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Corollary 3.1; de Groote, Observables I, PDF p./pp. 46.
-/
theorem solution {L : Type u} [CompleteBooleanAlgebra L] : HasFrameLaw L ↔ IsFiniteType L := by
  have hframe : HasFrameLaw L := by
    intro a s
    rw [inf_sSup_eq, sSup_image]
  have hfinite : IsFiniteType L := by
    intro s hs hd
    exact (frame_stone_extremally_disconnected hframe).2 s
  exact ⟨fun _ => hfinite, fun _ => hframe⟩

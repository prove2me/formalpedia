-- Prove2me | solution 1 for PlanarQueue.Planar.theorem_15
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T16:13:36.303184+00:00
-- url     : https://prove2.me/submissions/addfe5ae-177c-4b76-9113-0f75b03d75c3

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
import Theorems.Thm_PlanarQueue_Planar_planar_has_grid_minor_model
import Theorems.Thm_PlanarQueue_Planar_grid_model_quotient_no_K33_minor
import Theorems.Thm_PlanarQueue_Planar_planar_of_treewidth_three_no_K33_minor
import Theorems.Thm_PlanarQueue_Planar_theorem_15_core_grid_model

set_option autoImplicit false

namespace T15Red

open PlanarQueue.Planar

theorem isPlanar_mono {W : Type} {G H : SimpleGraph W} (hle : G ≤ H)
    (hH : RobertsonSeymour1986.GM5.IsPlanar H) : RobertsonSeymour1986.GM5.IsPlanar G := by
  obtain ⟨D⟩ := hH
  exact ⟨{ vertex := D.vertex
           vertex_injective := D.vertex_injective
           arc := fun h => D.arc (hle h)
           arc_injective := fun h => D.arc_injective (hle h)
           arc_reverse := fun h => D.arc_reverse (hle h)
           arc_avoids_vertices := fun h => D.arc_avoids_vertices (hle h)
           arcs_meet_only_at_endpoints := fun h k => D.arcs_meet_only_at_endpoints (hle h) (hle k) }⟩

theorem tw_mono {V : Type} [DecidableEq V] {G G' : SimpleGraph V} (hle : G' ≤ G)
    (h : RobertsonSeymour1986.GM5.TreewidthLE G 3) : RobertsonSeymour1986.GM5.TreewidthLE G' 3 := by
  obtain ⟨T, hT, t, X, ⟨h1, h2, h3, h4⟩, hw⟩ := h
  exact ⟨T, hT, t, X, ⟨h1, h2, fun x y hxy => h3 x y (hle hxy), h4⟩, hw⟩

theorem quotient_mono {V : Type} [Fintype V] [DecidableEq V] {G G' : SimpleGraph V}
    (hle : G ≤ G') (P : Finpartition (Finset.univ : Finset V)) :
    quotientGraph G P ≤ quotientGraph G' P := by
  intro A B h
  unfold quotientGraph at h ⊢
  rw [SimpleGraph.fromRel_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨v, hv, w, hw, hvw⟩ | ⟨v, hv, w, hw, hvw⟩
  · exact Or.inl ⟨v, hv, w, hw, hle hvw⟩
  · exact Or.inr ⟨v, hv, w, hw, hle hvw⟩

end T15Red

open PlanarQueue.Planar in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsPlanar G)
    (L : V → ℕ) (hL : IsBFSLayering G L) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ A ∈ P.parts, ∀ i : ℕ,
        (A.filter fun v => L v = i).card ≤ 3) ∧
      IsPlanar (quotientGraph G P) ∧
      RobertsonSeymour1986.GM5.TreewidthLE (quotientGraph G P) 3 := by
  have hGM := PlanarQueue.Planar.planar_has_grid_minor_model G hG
  obtain ⟨G', P, hle, hG', hconn, hw, htw⟩ :=
    PlanarQueue.Planar.theorem_15_core_grid_model G hGM L hL
  have hK := PlanarQueue.Planar.grid_model_quotient_no_K33_minor G' hG' P hconn
  have hpl := PlanarQueue.Planar.planar_of_treewidth_three_no_K33_minor _ htw hK
  have hq := T15Red.quotient_mono hle P
  exact ⟨P, hw, T15Red.isPlanar_mono hq hpl, T15Red.tw_mono hq htw⟩

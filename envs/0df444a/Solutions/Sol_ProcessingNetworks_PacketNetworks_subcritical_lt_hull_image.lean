-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.subcritical_lt_hull_image
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:28:16.009341+00:00
-- url     : https://prove2.me/submissions/1bb8496b-09d2-42d7-943e-f9225a879d82

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

namespace Cex14750acb

open ProcessingNetworks.PacketNetworks

/-- One packet class, no activities. -/
def dat : PacketNetworkData 1 0 := ⟨Fin.elim0, Fin.elim0⟩

/-- No activities and no links; the single (empty) configuration. -/
def cfg : LinkConfigData 0 0 :=
  ⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j, {fun _ => 0}⟩

/-- The single (empty) schedule. -/
def S : Finset (Fin 0 → ℕ) := {fun _ => 0}

theorem zero_mem_hull : (0 : Fin 0 → ℝ) ∈ hullFinset S := by
  unfold hullFinset
  apply subset_convexHull
  refine ⟨fun _ => 0, by simp [S], ?_⟩
  funext j
  exact Fin.elim0 j

theorem zero_mem_hullC : (0 : Fin 0 → ℝ) ∈ hullFinset cfg.C := by
  unfold hullFinset
  apply subset_convexHull
  refine ⟨fun _ => 0, by simp [cfg], ?_⟩
  funext j
  exact Fin.elim0 j

theorem mem_region : (0 : Fin 1 → ℝ) ∈ subcriticalRegion dat S cfg := by
  refine ⟨fun _ => le_refl 0, 0, zero_mem_hull, 0, zero_mem_hullC, ?_, fun k => Fin.elim0 k⟩
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem cex : ¬ (∃ shat ∈ hullFinset S, ∀ i, (0 : Fin 1 → ℝ) i < (R dat).mulVec shat i) := by
  rintro ⟨shat, -, h⟩
  have := h 0
  simp [Matrix.mulVec, dotProduct] at this

end Cex14750acb

open ProcessingNetworks.PacketNetworks in
theorem solution : ¬ (∀ {I J K : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (cfg : LinkConfigData J K) (lam : Fin I → ℝ) (hlam : lam ∈ subcriticalRegion dat S cfg),
    ∃ shat ∈ hullFinset S, ∀ i, lam i < (R dat).mulVec shat i) := by
  intro h
  exact Cex14750acb.cex (h Cex14750acb.dat Cex14750acb.S Cex14750acb.cfg 0 Cex14750acb.mem_region)

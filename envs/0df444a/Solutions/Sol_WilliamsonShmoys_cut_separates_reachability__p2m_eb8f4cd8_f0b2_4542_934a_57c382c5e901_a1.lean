-- Prove2me | solution 1 for WilliamsonShmoys.cut_separates_reachability__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:46:28.953038+00:00
-- url     : https://prove2.me/submissions/75c68a19-83e0-4417-a656-1ad798d1f2f7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem walk_membership_iff__p2m_144b642d_7706_43bd_a144_ab46103a2af1_a2
    {V : Type} (G : SimpleGraph V) (s : Set V) {u v : V}
    (p : G.Walk u v)
    (hcut : ∀ x y, G.Adj x y → (x ∈ s ↔ y ∈ s)) :
    (u ∈ s ↔ v ∈ s) := by
  induction p with
  | nil => rfl
  | cons hadj _ ih =>
      exact (hcut _ _ hadj).trans ih

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V} (s : Set V)
    (hu : u ∈ s) (hv : v ∉ s)
    (hcut : ∀ x y, G.Adj x y → (x ∈ s ↔ y ∈ s)) :
    ¬ G.Reachable u v := by
  intro hreach
  obtain ⟨p⟩ := hreach
  exact hv ((walk_membership_iff__p2m_144b642d_7706_43bd_a144_ab46103a2af1_a2
    G s p hcut).mp hu)
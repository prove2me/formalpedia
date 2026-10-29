-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_ordered_unreachable_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:39.489181+00:00
-- url     : https://prove2.me/submissions/1009c1ec-b79b-45f8-a86c-a9ae73d3bc31

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ G.Connected) :
    ∃ u v : V, ∃ S : Set V,
      u < v ∧
      ¬ G.Reachable u v ∧
      ¬ G.Adj u v ∧
      u ∈ S ∧
      v ∉ S ∧
      (∀ a b : V, a ∈ S → b ∉ S → ¬ G.Adj a b) := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : ¬ G.Preconnected := fun h => hNotConnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  obtain ⟨a, b, hab⟩ := hpre
  have key : ∀ u v : V, u < v → ¬ G.Reachable u v →
      ∃ u v : V, ∃ S : Set V,
        u < v ∧ ¬ G.Reachable u v ∧ ¬ G.Adj u v ∧ u ∈ S ∧ v ∉ S ∧
        (∀ a b : V, a ∈ S → b ∉ S → ¬ G.Adj a b) := by
    intro u v huv h
    refine ⟨u, v, {x | G.Reachable u x}, huv, h, fun hadj => h hadj.reachable,
      SimpleGraph.Reachable.refl u, h, ?_⟩
    intro x y hx hy hxy
    exact hy (SimpleGraph.Reachable.trans hx hxy.reachable)
  rcases lt_trichotomy a b with h | h | h
  · exact key a b h hab
  · exact absurd (h ▸ SimpleGraph.Reachable.refl a) hab
  · exact key b a h (fun h' => hab h'.symm)

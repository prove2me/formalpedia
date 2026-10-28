-- Prove2me | solution 1 for WilliamsonShmoys.connected_supergraph_of_component_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:39:20.308593+00:00
-- url     : https://prove2.me/submissions/1446875e-f4c1-438e-a21b-d14aa94354eb

import Mathlib
theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hcomp : ∀ G : SimpleGraph V, Nonempty (Fintype G.ConnectedComponent))
    (hstep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∀ (iG : Fintype G.ConnectedComponent),
        ∃ (H : SimpleGraph V), ∃ (iH : Fintype H.ConnectedComponent),
          G ≤ H ∧ P H ∧
            @Fintype.card H.ConnectedComponent iH <
              @Fintype.card G.ConnectedComponent iG) :
    ∀ G : SimpleGraph V, P G →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ P H := by
  classical
  suffices h : ∀ n : ℕ, ∀ G : SimpleGraph V, ∀ iG : Fintype G.ConnectedComponent,
      @Fintype.card G.ConnectedComponent iG = n → P G →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ P H by
    intro G hG
    obtain ⟨iG⟩ := hcomp G
    exact h _ G iG rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G iG hn hG
    by_cases hc : G.Connected
    · exact ⟨G, le_rfl, hc, hG⟩
    · obtain ⟨H, iH, hGH, hH, hlt⟩ := hstep G hG hc iG
      obtain ⟨K, hHK, hK, hPK⟩ := ih _ (hn ▸ hlt) H iH rfl hH
      exact ⟨K, hGH.trans hHK, hK, hPK⟩

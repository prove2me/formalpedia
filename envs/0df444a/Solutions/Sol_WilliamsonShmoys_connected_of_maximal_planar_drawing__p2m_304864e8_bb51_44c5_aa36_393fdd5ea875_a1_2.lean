-- Prove2me | solution 2 for WilliamsonShmoys.connected_of_maximal_planar_drawing__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:34.986688+00:00
-- url     : https://prove2.me/submissions/a5371f42-2b60-4ebd-8ef7-fcf14a6e5a7d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : ∀ Z : SimpleGraph V, Y.edgeSet ⊂ Z.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn Z), Y.Connected) := by
  intro h
  let Y : SimpleGraph Empty := ⊥
  have hY : WilliamsonShmoys.HasPlanarDrawingOn Y := by
    refine ⟨(fun x : Empty => x.elim), (fun x y t => x.elim), ?_, ?_, ?_⟩
    · intro a b
      exact Empty.elim a
    · intro u v huv hadj
      exact Empty.elim u
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      exact Empty.elim u
  have hmax : ∀ Z : SimpleGraph Empty, Y.edgeSet ⊂ Z.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn Z := by
    intro Z hsub hZ
    have hEq : Z = Y := Subsingleton.elim _ _
    subst Z
    exact hsub.2 (Set.Subset.rfl)
  have hnot : ¬ Y.Connected := by
    intro hc
    exact Empty.elim (Classical.choice hc.nonempty)
  have hc : Y.Connected := h (Y := Y) hY hmax
  exact hnot hc
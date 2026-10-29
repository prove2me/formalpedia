-- Prove2me | solution 2 for WilliamsonShmoys.finite_maximal_simpleGraph_property_extension__p2m_2d2efbeb_7ceb_4fa3_8371_f356ba71853f_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:11:17.488768+00:00
-- url     : https://prove2.me/submissions/319709b6-7bc5-4d79-b84a-4bb979f788e0

import Mathlib

set_option autoImplicit false

theorem _root_.solution
    {V : Type} [Fintype V]
    (T : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hT : P T) :
    ∃ R : SimpleGraph V,
      (∀ u v, T.Adj u v → R.Adj u v) ∧
      P R ∧
      (∀ S : SimpleGraph V,
        (∀ u v, T.Adj u v → S.Adj u v) →
        P S →
        (∀ u v, R.Adj u v → S.Adj u v) → S = R) := by
  have hF : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.Adj) (fun _ _ h => SimpleGraph.ext h)
  obtain ⟨R, hR⟩ := (Set.toFinite {R : SimpleGraph V | T ≤ R ∧ P R}).exists_maximal ⟨T, le_rfl, hT⟩
  exact ⟨R, fun u v h => hR.1.1 h, hR.1.2, fun S hTS hPS hRS =>
    le_antisymm (hR.2 ⟨fun u v h => hTS u v h, hPS⟩ (fun u v h => hRS u v h)) (fun u v h => hRS u v h)⟩

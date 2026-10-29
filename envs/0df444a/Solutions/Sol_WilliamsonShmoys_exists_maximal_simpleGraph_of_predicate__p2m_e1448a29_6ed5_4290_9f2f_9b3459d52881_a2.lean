-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_simpleGraph_of_predicate__p2m_e1448a29_6ed5_4290_9f2f_9b3459d52881_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:59:23.769993+00:00
-- url     : https://prove2.me/submissions/d6b83b4b-9791-4074-9980-560da0368a4d

import Mathlib

namespace S216WS

lemma exists_maximal {V : Type} [Fintype V] (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W) : ∃ H : SimpleGraph V, W ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  obtain ⟨H, ⟨hWH, hPH⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {G : SimpleGraph V | W ≤ G ∧ P G}) (Set.toFinite _) ⟨W, le_rfl, hP⟩
  exact ⟨H, hWH, hPH, fun K hHK hPK => le_antisymm (hmax ⟨le_trans hWH hHK, hPK⟩ hHK) hHK⟩

end S216WS


theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (R : SimpleGraph V)
    (hR : P R) :
    ∃ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) ∧
      P S ∧
      ∀ T : SimpleGraph V,
        (∀ u v, S.Adj u v → T.Adj u v) →
        P T →
        ∀ u v, T.Adj u v → S.Adj u v := by
  obtain ⟨H,h1,h2,h3⟩ := S216WS.exists_maximal R P hR
  exact ⟨H,fun u v h => h1 h,h2,fun T a b u v h => by rw [h3 T (fun x y hx => a x y hx) b] at h; exact h⟩

-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:10:30.802578+00:00
-- url     : https://prove2.me/submissions/53bf402f-e74d-4573-ad0c-4a0386ac8d59

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_element_of_finite_set__p2m_5ad4dfa2_7b03_4649_bf47_2550ad7ee6b8_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      (∀ {u v : V}, N.Adj u v → P.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (∀ Q : SimpleGraph V,
        (∀ {u v : V}, P.Adj u v → Q.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn Q →
        (∀ {u v : V}, Q.Adj u v → P.Adj u v)) := by
  classical
  let S : Set (SimpleGraph V) := {P | N ≤ P ∧ HasPlanarDrawingOn P}
  have hS : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨N, le_rfl, hN⟩
  obtain ⟨P, hPS, hPmax⟩ :=
    exists_maximal_element_of_finite_set__p2m_5ad4dfa2_7b03_4649_bf47_2550ad7ee6b8_a1 S hS hSne
  refine ⟨P, ?_, hPS.2, ?_⟩
  · intro u v huv
    exact hPS.1 huv
  · intro Q hPQ hQplanar u v huv
    have hPQle : P ≤ Q := fun {u v} huv => hPQ huv
    have hQle : Q ≤ P :=
      hPmax Q ⟨le_trans hPS.1 hPQle, hQplanar⟩ hPQle
    exact hQle huv
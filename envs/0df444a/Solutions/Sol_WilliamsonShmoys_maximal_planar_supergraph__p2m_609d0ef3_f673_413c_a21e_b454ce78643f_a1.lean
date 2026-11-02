-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_609d0ef3_f673_413c_a21e_b454ce78643f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:28:00.231481+00:00
-- url     : https://prove2.me/submissions/adc30681-550b-44ab-aa24-3dc706875389

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_maximal_of_strict_nat_measure__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
import Theorems.Thm_WilliamsonShmoys_simpleGraph_adjacency_card_strict__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W ≤ X ∧ HasPlanarDrawingOn X ∧
      ∀ Y : SimpleGraph V, X ≤ Y → HasPlanarDrawingOn Y → Y = X := by
  classical
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let P : SimpleGraph V → Prop := fun G => W ≤ G ∧ HasPlanarDrawingOn G
  let μ : SimpleGraph V → ℕ := fun G =>
    Fintype.card {p : V × V // G.Adj p.1 p.2}
  have hne : ∃ G, P G := ⟨W, le_rfl, hW⟩
  have hstrict : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → G ≠ H → μ G < μ H := by
    intro G H hGH hneGH
    exact WilliamsonShmoys.simpleGraph_adjacency_card_strict__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2 hGH hneGH
  obtain ⟨X, hXP, hXmax⟩ :=
    WilliamsonShmoys.finite_maximal_of_strict_nat_measure__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2 P μ hstrict hne
  refine ⟨X, hXP.1, hXP.2, ?_⟩
  intro Y hXY hY
  exact hXmax Y ⟨le_trans hXP.1 hXY, hY⟩ hXY

-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph_of_hereditary__p2m_cf95c127_ee46_41b0_beca_773ede50ca42_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:24:39.323003+00:00
-- url     : https://prove2.me/submissions/d5a55fe1-45c8-43e1-91d7-5a9f31f696ae

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hHer : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A)
    (X : SimpleGraph V) (hX : P X) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧ P Y ∧
      ∀ Z : SimpleGraph V, Y ≤ Z → P Z → Z = Y := by
  classical
  let Q : SimpleGraph V → Prop := fun Y => X ≤ Y ∧ P Y
  obtain ⟨Y, hXY, hmax⟩ :=
    Finite.exists_le_maximal (p := Q) (a := X) ⟨le_rfl, hX⟩
  have hQY : Q Y := (maximal_iff_forall_gt.mp hmax).1
  refine ⟨Y, hXY, hQY.2, ?_⟩
  intro Z hYZ hPZ
  have hQZ : Q Z := ⟨hXY.trans hYZ, hPZ⟩
  have hZY : Z ≤ Y := by
    by_contra h
    have hlt : Y < Z := lt_iff_le_not_ge.mpr ⟨hYZ, h⟩
    exact (maximal_iff_forall_gt.mp hmax).2 hlt hQZ
  exact le_antisymm hZY hYZ
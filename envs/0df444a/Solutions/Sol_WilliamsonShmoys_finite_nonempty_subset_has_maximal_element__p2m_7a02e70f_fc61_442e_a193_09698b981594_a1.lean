-- Prove2me | solution 1 for WilliamsonShmoys.finite_nonempty_subset_has_maximal_element__p2m_7a02e70f_fc61_442e_a193_09698b981594_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:32.33469+00:00
-- url     : https://prove2.me/submissions/34adcf79-d3c1-489f-b92a-6c91396c718a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (s : α → Prop)
    (hne : ∃ x, s x) :
    ∃ x, s x ∧ ∀ y, x ≤ y → s y → y = x := by
  obtain ⟨x, hx, hmax⟩ := ({x | s x} : Set α).toFinite.exists_maximal
    ⟨hne.choose, hne.choose_spec⟩
  refine ⟨x, hx, fun y hxy hy => ?_⟩
  exact le_antisymm (hmax hy hxy) hxy
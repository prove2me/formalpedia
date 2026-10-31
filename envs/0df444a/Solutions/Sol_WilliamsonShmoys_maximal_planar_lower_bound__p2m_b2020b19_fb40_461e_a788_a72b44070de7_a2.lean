-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_lower_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:04:07.297016+00:00
-- url     : https://prove2.me/submissions/171aed09-369a-43dc-a4b8-ea41a04912f2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion__p2m_715939c0_b6e9_4c03_a6f3_4355f1ffabc5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hsub, hL, hLbound⟩ :=
    WilliamsonShmoys.maximal_planar_completion__p2m_715939c0_b6e9_4c03_a6f3_4355f1ffabc5_a1
      K hK hV
  have hEq : K.edgeSet = L.edgeSet := by
    apply Set.Subset.antisymm hsub
    intro e he
    by_contra hne
    have hstrict : K.edgeSet ⊂ L.edgeSet :=
      Set.ssubset_iff_subset_ne.mpr ⟨hsub, by
        intro heq
        exact hne (heq.symm ▸ he)⟩
    exact (hmax L hstrict) hL
  have hcard : K.edgeSet.ncard = L.edgeSet.ncard := congrArg Set.ncard hEq
  calc
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := hLbound
    _ = K.edgeSet.ncard + 6 := by rw [← hcard]
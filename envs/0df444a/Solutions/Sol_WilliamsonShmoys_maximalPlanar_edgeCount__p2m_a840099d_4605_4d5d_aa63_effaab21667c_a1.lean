-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanar_edgeCount__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:44:01.861619+00:00
-- url     : https://prove2.me/submissions/82b8a1e6-18ea-4276-9e73-2fe38134299d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarEdgeBound__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
import Theorems.Thm_WilliamsonShmoys_planarTriangulationExtension__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      HasPlanarDrawingOn M →
      (letI : DecidableRel L.Adj := dL
       letI : DecidableRel M.Adj := dM
       L.edgeFinset ⊆ M.edgeFinset) →
      (letI : DecidableRel L.Adj := dL
       letI : DecidableRel M.Adj := dM
       L.edgeFinset = M.edgeFinset))
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := dL
     L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel L.Adj := dL
  have hupper := WilliamsonShmoys.planarEdgeBound__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1 L dL hL hn
  obtain ⟨M, dM, hM, hsub, hMcard⟩ :=
    WilliamsonShmoys.planarTriangulationExtension__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1 L dL hL hn
  have heq : L.edgeFinset = M.edgeFinset := by
    exact hmax M dM hM (by simpa using hsub)
  rw [heq]
  exact hMcard
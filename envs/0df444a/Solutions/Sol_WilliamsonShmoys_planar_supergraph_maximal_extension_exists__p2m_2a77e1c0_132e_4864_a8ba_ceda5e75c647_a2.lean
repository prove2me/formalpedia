-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension_exists__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:24:08.873241+00:00
-- url     : https://prove2.me/submissions/71afc2ba-5ab0-4920-9458-3e37164bd36a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    Exists fun H : SimpleGraph V =>
      G <= H /\
      HasPlanarDrawingOn H /\
      G.edgeSet.ncard <= H.edgeSet.ncard /\
      H.Connected /\
      (forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H) := by
  classical
  let p : SimpleGraph V → Prop := fun H => G ≤ H ∧ HasPlanarDrawingOn H
  have hpG : p G := ⟨le_rfl, hplanar⟩
  obtain ⟨H, _hGH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpH, hmax'⟩
  have hsub : G.edgeSet ⊆ H.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hpH.1
  have hfin : H.edgeSet.Finite := Set.toFinite _
  refine ⟨H, hpH.1, hpH.2, Set.ncard_le_ncard hsub hfin,
    SimpleGraph.Connected.mono hpH.1 hconn, ?_⟩
  intro K hHK hK
  have hKH : K ≤ H := hmax' ⟨hpH.1.trans hHK, hK⟩ hHK
  exact le_antisymm hKH hHK

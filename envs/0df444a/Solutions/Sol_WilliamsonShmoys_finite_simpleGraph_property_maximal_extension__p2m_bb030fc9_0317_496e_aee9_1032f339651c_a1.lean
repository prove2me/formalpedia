-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_property_maximal_extension__p2m_bb030fc9_0317_496e_aee9_1032f339651c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:13.184196+00:00
-- url     : https://prove2.me/submissions/5b9ec603-6d9f-4823-bc19-c6569821b0a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ (L : SimpleGraph V), H ≤ L ∧ P L ∧
      ∀ (K : SimpleGraph V), L ≤ K → P K → K = L := by
  classical
  let s : Set (SimpleGraph V) := {K | H ≤ K ∧ P K}
  have hs : s.Finite := Set.toFinite s
  have hne : s.Nonempty := ⟨H, le_rfl, hP⟩
  obtain ⟨L, hL⟩ := hs.exists_maximal hne
  refine ⟨L, hL.1.1, hL.1.2, ?_⟩
  intro K hLK hPK
  have hKmem : K ∈ s := ⟨le_trans hL.1.1 hLK, hPK⟩
  have hKL : K ≤ L := hL.2 hKmem hLK
  exact le_antisymm hKL hLK

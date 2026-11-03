-- Prove2me | solution 1 for WilliamsonShmoys.component_statistics__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:35:17.853436+00:00
-- url     : https://prove2.me/submissions/600a7344-5b3e-4552-9101-f989d4dade62

import Theorems.Thm_WilliamsonShmoys_component_statistics__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hconnected : ∀ {U : Type} [Fintype U] [LinearOrder U]
      (N : SimpleGraph U) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N → N.Connected → 3 ≤ Fintype.card U →
      N.edgeFinset.card ≤ 3 * Fintype.card U - 6)
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M) :
    ∃ parts : List (Nat × Nat),
      (parts.map Prod.fst).sum = Fintype.card V ∧
      (parts.map Prod.snd).sum = M.edgeFinset.card ∧
      ∀ p ∈ parts,
        (3 ≤ p.1 → p.2 ≤ 3 * p.1 - 6) ∧
        (p.1 < 3 → p.2 ≤ p.1) :=
  WilliamsonShmoys.component_statistics__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2 hconnected M dM hM
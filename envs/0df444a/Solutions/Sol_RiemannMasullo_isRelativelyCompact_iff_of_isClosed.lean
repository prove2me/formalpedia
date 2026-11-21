-- Prove2me | solution 1 for RiemannMasullo.isRelativelyCompact_iff_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:30:29.932766+00:00
-- url     : https://prove2.me/submissions/d610d821-3ba5-478b-a884-a1bac7033c0c

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L189-L191
import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
open RiemannMasullo


theorem solution {E : Type*} [TopologicalSpace E] [T2Space E]
    {A : Set E} (hA : IsClosed A) : IsRelativelyCompact A ↔ IsCompact A := by
  rw [IsRelativelyCompact, hA.closure_eq]

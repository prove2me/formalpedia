-- Prove2me | solution 1 for RiemannMasullo.balanced_iff_closedUnitDisc
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:20:54.331202+00:00
-- url     : https://prove2.me/submissions/f8baea0c-d64a-47da-8042-9cf04abe1d3a

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L35-L37
import Mathlib

open Set Filter Topology TopologicalSpace Bornology

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E] (A : Set E) :
    Balanced ℂ A ↔ ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ x ∈ A, z • x ∈ A :=
  balanced_iff_smul_mem

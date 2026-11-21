-- Prove2me | solution 1 for RiemannMasullo.directSumSeminorm_lof
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:26:15.087096+00:00
-- url     : https://prove2.me/submissions/138be2f5-0844-4c8f-9af2-0fc0b034f5ec

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Analysis/Normed/Module/Seminorm/DirectSum.lean#L35-L37
import Definitions.Def_RiemannMasullo_DirectSumSeminorm

open scoped DirectSum
open RiemannMasullo
variable {𝕜 ι : Type*} {X : ι → Type*}
  [NormedField 𝕜] [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  [DecidableEq ι] [∀ (i : ι) (z : X i), Decidable (z ≠ 0)]

theorem solution (p : ∀ i, Seminorm 𝕜 (X i)) (i : ι) (x : X i) :
    directSumSeminorm p (DirectSum.lof 𝕜 ι X i x) = p i x := by
  exact DFinsupp.sum_single_index (h := fun i ↦ p i) (map_zero (p i))

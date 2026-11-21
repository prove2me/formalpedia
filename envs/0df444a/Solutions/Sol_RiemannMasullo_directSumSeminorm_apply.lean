-- Prove2me | solution 1 for RiemannMasullo.directSumSeminorm_apply
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:26:14.326967+00:00
-- url     : https://prove2.me/submissions/0fec3152-3345-4562-827d-fe6f463ec2ff

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Analysis/Normed/Module/Seminorm/DirectSum.lean#L28-L31
import Definitions.Def_RiemannMasullo_DirectSumSeminorm

open scoped DirectSum
open RiemannMasullo
variable {𝕜 ι : Type*} {X : ι → Type*}
  [NormedField 𝕜] [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  [DecidableEq ι] [∀ (i : ι) (z : X i), Decidable (z ≠ 0)]

theorem solution (p : ∀ i, Seminorm 𝕜 (X i)) (x : ⨁ i, X i) (s : Finset ι)
    (hs : x.support ⊆ s) :
    directSumSeminorm p x = ∑ i ∈ s, p i (x i) := by
  exact DFinsupp.sum_of_support_subset hs fun i _ ↦ map_zero (p i)

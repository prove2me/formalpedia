-- Prove2me | solution 1 for RiemannMasullo.infiniteIdeleNorm_ker_closed
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:15:56.406446+00:00
-- url     : https://prove2.me/submissions/606ea9fe-1cdd-47dc-9a90-a26c090ad5e7

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L64-L65
import Mathlib
import Theorems.Thm_RiemannMasullo_infiniteIdeleNorm_continuous
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

theorem solution : IsClosed (N∞ : Set 𝕀∞) := by
  exact isClosed_singleton.preimage (infiniteIdeleNorm_continuous F)

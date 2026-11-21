-- Prove2me | solution 1 for RiemannMasullo.infiniteIdeleLog_continuous
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:15:53.885683+00:00
-- url     : https://prove2.me/submissions/7bccfc5c-dcf5-4f8d-8a10-56cc0551b5d3

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L83-L84
import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

theorem solution : Continuous (infiniteIdeleLog F) := by
  apply continuous_pi
  intro v
  have h : Continuous (fun g : (InfiniteAdeleRing F)ˣ ↦ g.val v) :=
    (continuous_apply v).comp Units.continuous_val
  exact continuous_const.mul (h.norm.log fun g ↦ norm_ne_zero_iff.mpr
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom g).ne_zero)

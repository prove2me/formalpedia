-- Prove2me | solution 1 for RiemannMasullo.infiniteIdeleLog_mul
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:15:53.155925+00:00
-- url     : https://prove2.me/submissions/bded7fec-8e7d-496e-9520-f7b93b7eab99

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L78-L80
import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

theorem solution (g h : 𝕀∞) :
    infiniteIdeleLog F (g * h) = infiniteIdeleLog F g + infiniteIdeleLog F h := by
  funext v
  have hn (x : (InfiniteAdeleRing F)ˣ) : x.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom x).ne_zero
  change (v.mult : ℝ) * Real.log ‖g.val v * h.val v‖ = _ + _
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hn g)) (norm_ne_zero_iff.mpr (hn h)), mul_add]
  rfl

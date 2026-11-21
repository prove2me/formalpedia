-- Prove2me | solution 1 for RiemannMasullo.infiniteIdeleLog_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:15:54.630222+00:00
-- url     : https://prove2.me/submissions/d9be76b4-1db7-4cde-8f69-0e270293dd1d

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L88-L97
import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

theorem solution (g : N∞) : ∑ v, infiniteIdeleLog F g.val v = 0 := by
  have hne (v : InfinitePlace F) : g.val.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom g.val).ne_zero
  have hprod := congrArg (fun u : ℝ≥0ˣ ↦ ((u : ℝ≥0) : ℝ))
    (show infiniteIdeleNorm F g.val = 1 from g.property)
  simp [infiniteIdeleNorm, Units.coe_prod] at hprod
  change ∏ v : InfinitePlace F, ‖g.val.val v‖ ^ v.mult = 1 at hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_prod (fun v _ ↦ pow_ne_zero v.mult (norm_ne_zero_iff.mpr (hne v)))] at hlog
  simpa only [infiniteIdeleLog, Real.log_pow, Real.log_one] using hlog

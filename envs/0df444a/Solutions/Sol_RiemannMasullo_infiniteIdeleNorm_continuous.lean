-- Prove2me | solution 1 for RiemannMasullo.infiniteIdeleNorm_continuous
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:29:53.761441+00:00
-- url     : https://prove2.me/submissions/811e8104-a720-40c8-bc47-1f5fa5f9f6ca

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L60-L61
import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

theorem solution : Continuous (infiniteIdeleNorm F) := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun g : (InfiniteAdeleRing F)ˣ ↦ ((infiniteIdeleNorm F g : ℝ≥0ˣ) : ℝ≥0))
  have heq : (fun g : (InfiniteAdeleRing F)ˣ ↦ ((infiniteIdeleNorm F g : ℝ≥0ˣ) : ℝ≥0)) =
      fun g ↦ ∏ v : InfinitePlace F, ‖g.val v‖₊ ^ v.mult := by
    funext g
    simp [infiniteIdeleNorm, Units.coe_prod]
    rfl
  rw [heq]
  apply continuous_finset_prod
  intro v _
  have h : Continuous (fun g : (InfiniteAdeleRing F)ˣ ↦ g.val v) :=
    (continuous_apply v).comp Units.continuous_val
  exact h.nnnorm.pow _

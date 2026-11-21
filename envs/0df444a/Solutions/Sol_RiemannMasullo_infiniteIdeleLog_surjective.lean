-- Prove2me | solution 1 for RiemannMasullo.infiniteIdeleLog_surjective
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:15:52.307209+00:00
-- url     : https://prove2.me/submissions/a67c7158-1388-442f-a580-06c221c3474a

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L74-L75
import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

theorem solution : Surjective (infiniteIdeleLog F) := by
  classical
  intro y
  have localNorm (v : InfinitePlace F) (t : ℝ) (ht : 0 < t) : ∃ z : v.Completion, ‖z‖ = t := by
    by_cases hv : v.IsReal
    · let e := ringEquivRealOfIsReal hv
      refine ⟨e.symm t, ?_⟩
      exact ((isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
        (map_zero e.symm) t).trans (Real.norm_of_nonneg ht.le)
    · have hw := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let e := ringEquivComplexOfIsComplex hw
      refine ⟨e.symm (t : ℂ), ?_⟩
      exact ((isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero
        (map_zero e.symm) (t : ℂ)).trans (Complex.norm_of_nonneg ht.le)
  choose z hz using fun v : InfinitePlace F ↦ localNorm v _ (Real.exp_pos (y v / v.mult))
  have hn (v : InfinitePlace F) : z v ≠ 0 := norm_pos_iff.mp ((hz v).symm ▸ Real.exp_pos _)
  let g : (InfiniteAdeleRing F)ˣ := Units.mkOfMulEqOne z (fun v ↦ (z v)⁻¹)
    (by funext v; exact mul_inv_cancel₀ (hn v))
  refine ⟨g, ?_⟩
  funext v
  change (v.mult : ℝ) * Real.log ‖z v‖ = y v
  rw [hz, Real.log_exp]
  have h : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero
  field_simp

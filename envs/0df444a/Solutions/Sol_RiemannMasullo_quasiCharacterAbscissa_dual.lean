-- Prove2me | solution 1 for RiemannMasullo.quasiCharacterAbscissa_dual
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:49:08.742185+00:00
-- url     : https://prove2.me/submissions/3d411e6c-e476-4d77-a400-7804d062e547

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L178-L191
import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

theorem solution [IsTopologicalGroup G] (hm : IsProperMap m)
    (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) :
    quasiCharacterAbscissa m hm hne (dualQuasiCharacter m hm.continuous c) =
      1 - quasiCharacterAbscissa m hm hne c := by
  let g := hne.choose
  have hmod : 0 < modℝ g := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)
  have hmod_one : modℝ g ≠ 1 := fun h =>
    hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hmod hmod_one
  have hnorm : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  change Real.log ‖(modℝ g : ℂ) * c (g⁻¹)‖ / Real.log (modℝ g) =
    1 - Real.log ‖c g‖ / Real.log (modℝ g)
  rw [map_inv, ← div_eq_mul_inv, norm_div, Complex.norm_of_nonneg hmod.le,
    Real.log_div hmod.ne' hnorm, sub_div, div_self hlog]

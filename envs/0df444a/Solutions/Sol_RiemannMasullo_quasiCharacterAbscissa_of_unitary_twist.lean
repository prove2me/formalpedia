-- Prove2me | solution 1 for RiemannMasullo.quasiCharacterAbscissa_of_unitary_twist
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:49:07.266419+00:00
-- url     : https://prove2.me/submissions/6253d646-b063-40c7-b4ba-335d5524351e

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L100-L111
import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

theorem solution (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (χ : PontryaginDual G) (s : ℂ)
    (hc : ∀ g, c g = (χ g : ℂ) * (modℝ g : ℂ) ^ s) :
    quasiCharacterAbscissa m hm hne c = s.re := by
  let g := hne.choose
  have hmod : 0 < modℝ g := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)
  have hmod_one : modℝ g ≠ 1 := fun h =>
    hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hmod hmod_one
  change Real.log ‖c g‖ / Real.log (modℝ g) = s.re
  rw [hc g, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hmod,
    Real.log_rpow hmod, mul_div_cancel_right₀ _ hlog]

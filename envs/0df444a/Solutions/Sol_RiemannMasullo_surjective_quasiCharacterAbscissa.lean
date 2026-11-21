-- Prove2me | solution 1 for RiemannMasullo.surjective_quasiCharacterAbscissa
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:49:09.463067+00:00
-- url     : https://prove2.me/submissions/2f6f2d15-7766-46f0-8d24-69637b1a6b04

-- Statement from mccorvie/riemann-masullo, Apache-2.0. New proof for Prove2Me.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L130-L132
import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

theorem solution (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Surjective (quasiCharacterAbscissa m hm hne) := by
  intro t
  let M : G →* ℝ := NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp m)
  have hp (g : G) : 0 < M g := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)
  have hc : Continuous M :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hm.continuous)
  let p : G →* ℝ :=
    { toFun := fun g ↦ (M g) ^ t
      map_one' := by simp
      map_mul' := fun g h ↦ by rw [map_mul, Real.mul_rpow (hp g).le (hp h).le] }
  let c : QuasiCharacter G :=
    ⟨Complex.ofRealHom.toMonoidHom.comp p, Complex.continuous_ofReal.comp
      (hc.rpow_const (p := t) fun g ↦ Or.inl (hp g).ne')⟩
  refine ⟨c, ?_⟩
  let g := hne.choose
  have h1 : M g ≠ 1 := fun h ↦ hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
  change Real.log ‖((M g ^ t : ℝ) : ℂ)‖ / Real.log (M g) = t
  rw [Complex.norm_of_nonneg (Real.rpow_nonneg (hp g).le t), Real.log_rpow (hp g),
    mul_div_cancel_right₀ _ (Real.log_ne_zero_of_pos_of_ne_one (hp g) h1)]

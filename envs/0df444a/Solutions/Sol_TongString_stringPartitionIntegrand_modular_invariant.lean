-- Prove2me | solution 1 for TongString.stringPartitionIntegrand_modular_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:11:23.515975+00:00
-- url     : https://prove2.me/submissions/03b14a3c-5a13-4f7e-bce8-a936f995652c

import Mathlib
import Definitions.Def_TongString_modular_action
import Definitions.Def_TongString_partition_functions

namespace TongString

open Complex UpperHalfPlane MatrixGroups

lemma dedekindEta_eq_eta (τ : ℂ) : dedekindEta τ = ModularForm.eta τ := by
  unfold dedekindEta ModularForm.eta
  simp only [ModularForm.eta_q_eq_cexp, Function.Periodic.qParam]
  congr 2

lemma norm_eta_pow48 (z : ℍ) :
    ‖ModularForm.eta (z : ℂ)‖ ^ 48 = ‖ModularForm.discriminant z‖ ^ 2 := by
  unfold ModularForm.discriminant
  rw [norm_pow, ← pow_mul]

lemma disc_transform (γ : SL(2, ℤ)) (z : ℍ) :
    ModularForm.discriminant ((Matrix.SpecialLinearGroup.mapGL ℝ γ) • z) =
      (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) ^ (12 : ℤ) * ModularForm.discriminant z := by
  have h := SlashInvariantForm.slash_action_eqn' (Γ := 𝒮ℒ) CuspForm.discriminant
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) z
  simpa using h

lemma smul_coe (γ : SL(2, ℤ)) (z : ℍ) :
    (((Matrix.SpecialLinearGroup.mapGL ℝ γ) • z : ℍ) : ℂ) =
      (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) /
        (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  have := UpperHalfPlane.coe_specialLinearGroup_apply γ z
  change ((γ • z : ℍ) : ℂ) = _
  rw [this]
  simp

lemma smul_im (γ : SL(2, ℤ)) (z : ℍ) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ) • z : ℍ).im =
      z.im / Complex.normSq (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  have := UpperHalfPlane.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
  rw [this]
  simp [UpperHalfPlane.denom]

end TongString

open Complex UpperHalfPlane MatrixGroups in
open TongString in
theorem solution (a b c d : ℤ) (h : a * d - b * c = 1)
    (τ : ℂ) (hτ : 0 < τ.im) :
    stringPartitionIntegrand (modularAction a b c d τ) = stringPartitionIntegrand τ := by
  have hdet : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [Matrix.det_fin_two]; linarith
  set γ : SL(2, ℤ) := ⟨!![a, b; c, d], hdet⟩ with hγ
  set z : ℍ := ⟨τ, hτ⟩ with hz
  have hzτ : (z : ℂ) = τ := rfl
  have hcoe : modularAction a b c d τ = (((Matrix.SpecialLinearGroup.mapGL ℝ γ) • z : ℍ) : ℂ) := by
    rw [smul_coe]; simp [γ, modularAction, hzτ]
  have him := smul_im γ z
  have hD := disc_transform γ z
  have hden : (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) = (c : ℂ) * τ + d := by
    simp [γ, hzτ]
  rw [hden] at him hD
  have hJ : (c : ℂ) * τ + d ≠ 0 := by
    rw [← hden]; exact UpperHalfPlane.denom_ne_zero γ z
  have hJn : ‖(c : ℂ) * τ + d‖ ≠ 0 := norm_ne_zero_iff.mpr hJ
  have hΔ : ‖ModularForm.discriminant z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (ModularForm.discriminant_ne_zero z)
  have hτn : τ.im ≠ 0 := hτ.ne'
  rw [hcoe]
  unfold stringPartitionIntegrand
  have hη : ‖ModularForm.eta τ‖ ^ 48 = ‖ModularForm.discriminant z‖ ^ 2 := norm_eta_pow48 z
  rw [dedekindEta_eq_eta, dedekindEta_eq_eta, UpperHalfPlane.coe_im, him]
  simp only [one_div_pow]
  rw [norm_eta_pow48 ((Matrix.SpecialLinearGroup.mapGL ℝ γ) • z), hη, hD, norm_mul,
    norm_zpow, Complex.normSq_eq_norm_sq, show z.im = τ.im from rfl]
  field_simp

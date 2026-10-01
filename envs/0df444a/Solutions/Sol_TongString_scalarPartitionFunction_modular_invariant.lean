-- Prove2me | solution 1 for TongString.scalarPartitionFunction_modular_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T16:44:25.659284+00:00
-- url     : https://prove2.me/submissions/85bc8bb7-daca-473c-b63e-624cc5476713

import Mathlib
import Definitions.Def_TongString_modular_action
import Definitions.Def_TongString_partition_functions

set_option autoImplicit false

open UpperHalfPlane in
lemma tong_e4e0_eta_eq (τ : ℂ) : TongString.dedekindEta τ = ModularForm.eta τ := by
  unfold TongString.dedekindEta ModularForm.eta
  simp only [ModularForm.eta_q_eq_cexp, Function.Periodic.qParam]
  push_cast
  ring_nf

open UpperHalfPlane MatrixGroups in
lemma tong_e4e0_norm_eta_sq (γ : SL(2, ℤ)) (z : ℍ) :
    ‖ModularForm.eta ((γ • z : ℍ) : ℂ)‖ ^ 2 = ‖denom γ z‖ * ‖ModularForm.eta (z : ℂ)‖ ^ 2 := by
  have h1 : CuspForm.discriminant (γ • z) = denom γ z ^ (12 : ℤ) * CuspForm.discriminant z :=
    SlashInvariantForm.slash_action_eqn'' (Γ := (Matrix.SpecialLinearGroup.mapGL ℝ).range)
      (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ) CuspForm.discriminant
      (MonoidHom.mem_range.2 ⟨γ, rfl⟩) z
  simp only [CuspForm.coe_discriminant, ModularForm.discriminant] at h1
  have h2 : (‖ModularForm.eta ((γ • z : ℍ) : ℂ)‖ ^ 2) ^ 12 =
      (‖denom γ z‖ * ‖ModularForm.eta (z : ℂ)‖ ^ 2) ^ 12 := by
    have := congrArg (fun x : ℂ => ‖x‖) h1
    simp only [norm_mul, norm_pow, norm_zpow] at this
    rw [← pow_mul, mul_pow, ← pow_mul]
    norm_num
    exact_mod_cast this
  exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).1 h2

open UpperHalfPlane MatrixGroups in
theorem solution (a b c d : ℤ) (h : a * d - b * c = 1) (τ : ℂ)
    (hτ : 0 < τ.im) :
    TongString.scalarPartitionFunction (TongString.modularAction a b c d τ) =
      TongString.scalarPartitionFunction τ := by
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by simp [Matrix.det_fin_two]; linarith⟩
  let z : ℍ := ⟨τ, hτ⟩
  have hact : TongString.modularAction a b c d τ = ((γ • z : ℍ) : ℂ) := by
    rw [UpperHalfPlane.specialLinearGroup_apply]
    simp [TongString.modularAction, γ, z]
  have hkey := tong_e4e0_norm_eta_sq γ z
  have him := ModularGroup.im_smul_eq_div_normSq γ z
  have hD : 0 < ‖denom γ z‖ := norm_pos_iff.2 (denom_ne_zero _ _)
  have hE : 0 < ‖ModularForm.eta (z : ℂ)‖ :=
    norm_pos_iff.2 (ModularForm.eta_ne_zero z.im_pos)
  have hzi : z.im = τ.im := rfl
  have hzc : ModularForm.eta (z : ℂ) = ModularForm.eta τ := rfl
  rw [hact]
  unfold TongString.scalarPartitionFunction
  rw [tong_e4e0_eta_eq, tong_e4e0_eta_eq, one_div_pow, one_div_pow, hkey,
    UpperHalfPlane.coe_im, him, Complex.normSq_eq_norm_sq, Real.sqrt_div z.im_pos.le,
    Real.sqrt_sq hD.le, hzi, hzc]
  rw [hzc] at hE
  have hs : 0 < Real.sqrt τ.im := Real.sqrt_pos.2 hτ
  field_simp

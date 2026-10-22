-- Prove2me | solution 1 for SensitivityPoA.NoUniform.eq_3_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:37:59.057005+00:00
-- url     : https://prove2.me/submissions/895e3ac8-7096-4f09-9048-527ecf35c49c

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_NoUniform_Setting

set_option autoImplicit false
open SensitivityPoA.NoUniform
open scoped Pointwise

theorem solution (N : Network) (Γ Γ' : Game N) (hΓ : Γ ∈ gameSpace N) (hΓ' : Γ' ∈ gameSpace N)
    (hd : Γ.d = Γ'.d) (υ : ℝ) (hυ : 0 < υ) :
    gameDist (costNormalize υ Γ) (costNormalize υ Γ') = gameDist Γ Γ' / υ := by
  have hυ0 : 0 ≤ υ⁻¹ := inv_nonneg.mpr hυ.le
  unfold gameDist
  simp only [costNormalize]
  rw [hd]
  simp only [sub_self, norm_zero]
  have hS : (fun p : Fin N.J × ℝ => |Γ.τ p.1 p.2 / υ - Γ'.τ p.1 p.2 / υ|) ''
        (Set.univ ×ˢ Set.Icc 0 (min (totalDemand Γ'.d) (totalDemand Γ'.d)))
      = υ⁻¹ • ((fun p : Fin N.J × ℝ => |Γ.τ p.1 p.2 - Γ'.τ p.1 p.2|) ''
        (Set.univ ×ˢ Set.Icc 0 (min (totalDemand Γ'.d) (totalDemand Γ'.d)))) := by
    rw [← Set.image_smul, Set.image_image]
    refine Set.image_congr (fun p _ => ?_)
    rw [← sub_div, abs_div, abs_of_pos hυ, smul_eq_mul]
    ring
  have hn : ‖fun j => Γ.τ j (totalDemand Γ'.d) / υ - Γ'.τ j (totalDemand Γ'.d) / υ‖
      = υ⁻¹ * ‖fun j => Γ.τ j (totalDemand Γ'.d) - Γ'.τ j (totalDemand Γ'.d)‖ := by
    have : (fun j => Γ.τ j (totalDemand Γ'.d) / υ - Γ'.τ j (totalDemand Γ'.d) / υ)
        = υ⁻¹ • (fun j => Γ.τ j (totalDemand Γ'.d) - Γ'.τ j (totalDemand Γ'.d)) := by
      ext j; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this, norm_smul, Real.norm_of_nonneg hυ0]
  rw [hS, hn, Real.sSup_smul_of_nonneg hυ0, smul_eq_mul, div_eq_inv_mul]
  simp only [mul_max_of_nonneg _ _ hυ0, mul_zero]

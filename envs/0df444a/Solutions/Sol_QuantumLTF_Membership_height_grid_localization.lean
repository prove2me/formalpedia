-- Prove2me | solution 1 for QuantumLTF.Membership.height_grid_localization
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T19:02:10.872127+00:00
-- url     : https://prove2.me/submissions/3050972b-ee93-4fb3-ab58-a700836819f5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
import Theorems.Thm_QuantumLTF_Membership_height_rho_grid_affine
import Theorems.Thm_QuantumLTF_Membership_norm_gridVec_le
import Theorems.Thm_QuantumLTF_Membership_rho_sqrt_le

open QAlgorithms
open QuantumLTF.Membership

theorem solution {n b : ℕ}
    (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (w p : EuclideanSpace ℝ (Fin n)) (θ htil : ℝ)
    (hw : ‖w‖ = 1) (ha : 1 / 10 ≤ |inner ℝ w p|)
    (hhtil : |htil - height w θ p 0| ≤ ε / 100)
    (x : Fin n → Qubits b) :
    |height w θ p (rho n • gridVec n b x) - htil| ≤ 1 / 4 := by
  have hane : inner ℝ w p ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at ha
    norm_num at ha
  rw [height_rho_grid_affine w p θ x hane]
  have hρ : 0 ≤ rho n := by unfold rho; positivity
  have hgrid := norm_gridVec_le n b x
  have hinner : |inner ℝ w (gridVec n b x)| ≤ Real.sqrt n / 2 := by
    calc
      |inner ℝ w (gridVec n b x)| ≤ ‖w‖ * ‖gridVec n b x‖ := by
        simpa [Real.norm_eq_abs] using
          (norm_inner_le_norm (𝕜 := ℝ) w (gridVec n b x))
      _ = ‖gridVec n b x‖ := by rw [hw, one_mul]
      _ ≤ Real.sqrt n / 2 := hgrid
  have hρsqrt := rho_sqrt_le n (le_trans (by decide : 1 ≤ 2) hn)
  have hnum : rho n * |inner ℝ w (gridVec n b x)| ≤ 1 / 80 := by
    calc
      rho n * |inner ℝ w (gridVec n b x)| ≤ rho n * (Real.sqrt n / 2) :=
        mul_le_mul_of_nonneg_left hinner hρ
      _ ≤ 1 / 80 := by nlinarith
  have habpos : 0 < |inner ℝ w p| := lt_of_lt_of_le (by norm_num) ha
  have hfrac : rho n * |inner ℝ w (gridVec n b x)| / |inner ℝ w p| ≤ 1 / 8 := by
    apply (div_le_iff₀ habpos).2
    nlinarith
  have hoff : |height w θ p 0 - htil| ≤ 1 / 200 := by
    rw [abs_sub_comm]
    nlinarith
  calc
    |height w θ p 0 - rho n * inner ℝ w (gridVec n b x) / inner ℝ w p - htil| =
        |(height w θ p 0 - htil) -
          rho n * inner ℝ w (gridVec n b x) / inner ℝ w p| := by ring
    _ ≤ |height w θ p 0 - htil| +
        |rho n * inner ℝ w (gridVec n b x) / inner ℝ w p| := abs_sub _ _
    _ = |height w θ p 0 - htil| +
        rho n * |inner ℝ w (gridVec n b x)| / |inner ℝ w p| := by
      rw [abs_div, abs_mul, abs_of_nonneg hρ]
    _ ≤ 1 / 4 := by nlinarith

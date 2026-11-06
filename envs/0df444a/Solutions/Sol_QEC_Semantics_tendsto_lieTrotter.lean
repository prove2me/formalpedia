-- Prove2me | solution 1 for QEC.Semantics.tendsto_lieTrotter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:46:35.975222+00:00
-- url     : https://prove2.me/submissions/709e45bc-f7ab-4d54-aad4-bc5c4eee948c

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Theorems.Thm_QEC_Semantics_norm_normedSpace_exp_le
import Theorems.Thm_QEC_Semantics_norm_pow_sub_pow_le
import Theorems.Thm_QEC_Semantics_tendsto_lieTrotter_localError
section
namespace QEC.Semantics
open Filter
open scoped Topology
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]
private theorem norm_referenceStep_pow_le (x y : A) {n k : Nat}
    (hn : 0 < n) (hk : k ≤ n) :
    ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y))‖ ^ k ≤
      Real.exp (‖x‖ + ‖y‖) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hkR : (k : Real) ≤ n := by exact_mod_cast hk
  calc
    ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y))‖ ^ k ≤
        (Real.exp ‖((n : Complex)⁻¹ • (x + y))‖) ^ k := by
      gcongr
      exact norm_normedSpace_exp_le _
    _ ≤ (Real.exp (((n : Real)⁻¹) * (‖x‖ + ‖y‖))) ^ k := by
      gcongr
      rw [norm_smul, norm_inv, RCLike.norm_natCast]
      gcongr
      exact norm_add_le x y
    _ = Real.exp ((k : Real) * (((n : Real)⁻¹) * (‖x‖ + ‖y‖))) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (‖x‖ + ‖y‖) := by
      apply Real.exp_le_exp.mpr
      have hratio : (k : Real) * (n : Real)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hnR]
        exact hkR
      calc
        (k : Real) * ((n : Real)⁻¹ * (‖x‖ + ‖y‖)) =
            ((k : Real) * (n : Real)⁻¹) * (‖x‖ + ‖y‖) := by ring
        _ ≤ 1 * (‖x‖ + ‖y‖) := by
          gcongr
        _ = ‖x‖ + ‖y‖ := one_mul _
private theorem norm_lieTrotterStep_pow_le (x y : A) {n k : Nat}
    (hn : 0 < n) (hk : k ≤ n) :
    ‖lieTrotterStep x y ((n : Complex)⁻¹)‖ ^ k ≤
      Real.exp (‖x‖ + ‖y‖) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hkR : (k : Real) ≤ n := by exact_mod_cast hk
  have hstep : ‖lieTrotterStep x y ((n : Complex)⁻¹)‖ ≤
      Real.exp (((n : Real)⁻¹) * (‖x‖ + ‖y‖)) := by
    calc
      ‖lieTrotterStep x y ((n : Complex)⁻¹)‖ ≤
          ‖NormedSpace.exp (((n : Complex)⁻¹) • x)‖ *
            ‖NormedSpace.exp (((n : Complex)⁻¹) • y)‖ := by
        exact norm_mul_le _ _
      _ ≤ Real.exp ‖((n : Complex)⁻¹) • x‖ *
            Real.exp ‖((n : Complex)⁻¹) • y‖ := by
        gcongr <;> exact norm_normedSpace_exp_le _
      _ = Real.exp (((n : Real)⁻¹) * (‖x‖ + ‖y‖)) := by
        rw [← Real.exp_add]
        congr 1
        simp [norm_smul, norm_inv]
        ring
  calc
    ‖lieTrotterStep x y ((n : Complex)⁻¹)‖ ^ k ≤
        (Real.exp (((n : Real)⁻¹) * (‖x‖ + ‖y‖))) ^ k := by
      gcongr
    _ = Real.exp ((k : Real) * (((n : Real)⁻¹) * (‖x‖ + ‖y‖))) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (‖x‖ + ‖y‖) := by
      apply Real.exp_le_exp.mpr
      have hratio : (k : Real) * (n : Real)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hnR]
        exact hkR
      calc
        (k : Real) * ((n : Real)⁻¹ * (‖x‖ + ‖y‖)) =
            ((k : Real) * (n : Real)⁻¹) * (‖x‖ + ‖y‖) := by ring
        _ ≤ 1 * (‖x‖ + ‖y‖) := by gcongr
        _ = ‖x‖ + ‖y‖ := one_mul _
private theorem norm_lieTrotter_power_defect_le (x y : A) {n : Nat}
    (hn : 0 < n) :
    ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y)) ^ n -
        (lieTrotterStep x y ((n : Complex)⁻¹)) ^ n‖ ≤
      (Real.exp (‖x‖ + ‖y‖) * Real.exp (‖x‖ + ‖y‖)) *
        ((n : Real) *
          ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y)) -
            lieTrotterStep x y ((n : Complex)⁻¹)‖) := by
  let u := NormedSpace.exp (((n : Complex)⁻¹) • (x + y))
  let v := lieTrotterStep x y ((n : Complex)⁻¹)
  let C := Real.exp (‖x‖ + ‖y‖)
  calc
    ‖u ^ n - v ^ n‖ ≤
        ∑ k ∈ Finset.range n,
          ‖u‖ ^ k * ‖u - v‖ * ‖v‖ ^ (n - 1 - k) :=
      norm_pow_sub_pow_le u v n
    _ ≤ ∑ k ∈ Finset.range n, C * ‖u - v‖ * C := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have htail : n - 1 - k ≤ n :=
        (Nat.sub_le (n - 1) k).trans (Nat.sub_le n 1)
      dsimp only [u, v, C]
      gcongr
      · exact norm_referenceStep_pow_le x y hn hkn.le
      · exact norm_lieTrotterStep_pow_le x y hn htail
    _ = C * C * ((n : Real) * ‖u - v‖) := by
      simp [C]
      ring
    _ = (Real.exp (‖x‖ + ‖y‖) * Real.exp (‖x‖ + ‖y‖)) *
        ((n : Real) *
          ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y)) -
            lieTrotterStep x y ((n : Complex)⁻¹)‖) := by rfl
private theorem normedSpace_exp_inv_nat_smul_pow (x : A) {n : Nat}
    (hn : 0 < n) :
    (NormedSpace.exp (((n : Complex)⁻¹) • x)) ^ n =
      NormedSpace.exp x := by
  have exp_nsmul_complex (m : Nat) (z : A) :
      NormedSpace.exp (m • z) = NormedSpace.exp z ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [succ_nsmul, pow_succ,
          NormedSpace.exp_add_of_commute_of_mem_ball
            ((Commute.refl z).smul_left m)
            ((NormedSpace.expSeries_radius_eq_top Complex A).symm ▸
              edist_lt_top _ _)
            ((NormedSpace.expSeries_radius_eq_top Complex A).symm ▸
              edist_lt_top _ _), ih]
  rw [← exp_nsmul_complex]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul Complex, smul_smul]
  have hnC : (n : Complex) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [mul_inv_cancel₀ hnC, one_smul]
end
end QEC.Semantics
end

set_option autoImplicit false
open QEC QEC.Semantics
open Filter
open scoped Topology
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]
namespace QEC.Semantics
theorem _root_.solution (x y : A) :
    Tendsto
      (fun n : Nat => (lieTrotterStep x y ((n : Complex)⁻¹)) ^ n)
      atTop (nhds (NormedSpace.exp (x + y))) := by
  let u : Nat → A := fun n => NormedSpace.exp (((n : Complex)⁻¹) • (x + y))
  let v : Nat → A := fun n => lieTrotterStep x y ((n : Complex)⁻¹)
  let C : Real := Real.exp (‖x‖ + ‖y‖) * Real.exp (‖x‖ + ‖y‖)
  let localError : Nat → Real := fun n => (n : Real) * ‖u n - v n‖
  have hlocal : Tendsto localError atTop (nhds 0) := by
    simpa [localError, u, v] using tendsto_lieTrotter_localError x y
  have hmajorant : Tendsto (fun n => C * localError n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hlocal)
  have hbound : ∀ᶠ n in atTop, ‖u n ^ n - v n ^ n‖ ≤ C * localError n := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    exact norm_lieTrotter_power_defect_le x y hn
  have hdefect : Tendsto (fun n => u n ^ n - v n ^ n) atTop (nhds 0) :=
    squeeze_zero_norm' hbound hmajorant
  have href : Tendsto (fun n => u n ^ n) atTop
      (nhds (NormedSpace.exp (x + y))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    exact (normedSpace_exp_inv_nat_smul_pow (x + y) hn).symm
  have hresult := href.sub hdefect
  convert hresult using 1 <;> simp [u, v]
end QEC.Semantics

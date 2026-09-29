-- Prove2me | solution 1 for SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/84828ab0-a41c-59af-8a18-396ec2a0d8f2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq

set_option autoImplicit false

open scoped SchwartzMap ContDiff

namespace WsC
namespace GS

open Real

noncomputable section

variable (ι : Type) [Fintype ι]

def q : EuclideanSpace ℝ ι → ℝ := fun x => (-Real.pi) * ‖x‖ ^ 2

def gR : EuclideanSpace ℝ ι → ℝ := Real.exp ∘ q ι

def gC : EuclideanSpace ℝ ι → ℂ := Complex.ofRealLI ∘ gR ι

theorem q_hasTemperateGrowth : (q ι).HasTemperateGrowth := by
  unfold q
  fun_prop

theorem q_contDiff : ContDiff ℝ ∞ (q ι) := (q_hasTemperateGrowth ι).1

theorem gR_contDiff : ContDiff ℝ ∞ (gR ι) := Real.contDiff_exp.comp (q_contDiff ι)

theorem gC_contDiff : ContDiff ℝ ∞ (gC ι) :=
  Complex.ofRealCLM.contDiff.comp (gR_contDiff ι)

theorem norm_iteratedFDeriv_exp (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp t‖ = Real.exp t := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

theorem gR_bound (n : ℕ) : ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x,
    ‖iteratedFDeriv ℝ n (gR ι) x‖ ≤ C * (1 + ‖x‖) ^ k * Real.exp (q ι x) := by
  obtain ⟨k, C₀, hC₀, hq⟩ := (q_hasTemperateGrowth ι).norm_iteratedFDeriv_le_uniform n
  refine ⟨k * n, (Nat.factorial n : ℝ) * (1 + C₀) ^ n, by positivity, fun x => ?_⟩
  set D : ℝ := (1 + C₀) * (1 + ‖x‖) ^ k with hD
  have h1x : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ (by simp [norm_nonneg])
  have hD1 : 1 ≤ D := by
    rw [hD]
    nlinarith
  have hbound : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i Real.exp (q ι x)‖ ≤ Real.exp (q ι x) := by
    intro i _
    rw [norm_iteratedFDeriv_exp]
  have hgrowth : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (q ι) x‖ ≤ D ^ i := by
    intro i hi hin
    calc ‖iteratedFDeriv ℝ i (q ι) x‖ ≤ C₀ * (1 + ‖x‖) ^ k := hq i hin x
      _ ≤ D := by rw [hD]; nlinarith
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
  have := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := q ι) Real.contDiff_exp (q_contDiff ι)
    (mod_cast le_top) x hbound hgrowth
  calc ‖iteratedFDeriv ℝ n (gR ι) x‖ ≤ (Nat.factorial n : ℝ) * Real.exp (q ι x) * D ^ n := this
    _ = (Nat.factorial n : ℝ) * (1 + C₀) ^ n * (1 + ‖x‖) ^ (k * n) * Real.exp (q ι x) := by
      rw [hD, mul_pow, ← pow_mul]; ring

theorem poly_gauss_le (M : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ M * Real.exp ((-Real.pi) * r ^ 2) ≤ Real.exp 2 * (Nat.factorial M : ℝ) := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have h1 : (-Real.pi) * r ^ 2 ≤ 2 - (1 + r) := by nlinarith [sq_nonneg (r - 1 / 6)]
  have h2 : (1 + r) ^ M / (Nat.factorial M : ℝ) ≤ Real.exp (1 + r) := Real.pow_div_factorial_le_exp (x := 1 + r) (hx := by linarith) (n := M)
  have hM : (0 : ℝ) < (Nat.factorial M : ℝ) := by positivity
  rw [div_le_iff₀ hM] at h2
  calc (1 + r) ^ M * Real.exp ((-Real.pi) * r ^ 2)
      ≤ (Real.exp (1 + r) * (Nat.factorial M : ℝ)) * Real.exp (2 - (1 + r)) := by
        apply mul_le_mul h2 (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (by positivity)
    _ = Real.exp 2 * (Nat.factorial M : ℝ) := by
        rw [mul_assoc, mul_comm ((Nat.factorial M : ℝ) : ℝ), ← mul_assoc, ← Real.exp_add]
        ring_nf

theorem gC_decay (m n : ℕ) : ∃ C : ℝ, ∀ x, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (gC ι) x‖ ≤ C := by
  obtain ⟨k, C, hC, hb⟩ := gR_bound ι n
  refine ⟨C * (Real.exp 2 * (Nat.factorial (m + k) : ℝ)), fun x => ?_⟩
  have hiso : ‖iteratedFDeriv ℝ n (gC ι) x‖ = ‖iteratedFDeriv ℝ n (gR ι) x‖ :=
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left (gR_contDiff ι).contDiffAt (mod_cast le_top)
  rw [hiso]
  have hxm : ‖x‖ ^ m ≤ (1 + ‖x‖) ^ m :=
    pow_le_pow_left₀ (norm_nonneg x) (by linarith [norm_nonneg x]) m
  have hpg := poly_gauss_le (m + k) ‖x‖ (norm_nonneg x)
  calc ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (gR ι) x‖
      ≤ (1 + ‖x‖) ^ m * (C * (1 + ‖x‖) ^ k * Real.exp (q ι x)) :=
        mul_le_mul hxm (hb x) (norm_nonneg _) (by positivity)
    _ = C * ((1 + ‖x‖) ^ (m + k) * Real.exp ((-Real.pi) * ‖x‖ ^ 2)) := by
        rw [q, pow_add]; ring
    _ ≤ C * (Real.exp 2 * (Nat.factorial (m + k) : ℝ)) := mul_le_mul_of_nonneg_left hpg hC

def gauss : 𝓢(EuclideanSpace ℝ ι, ℂ) where
  toFun := gC ι
  smooth' := gC_contDiff ι
  decay' := gC_decay ι

theorem gauss_apply (x : EuclideanSpace ℝ ι) :
    gauss ι x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ) := by
  show gC ι x = _
  simp [gC, gR, q, neg_mul]

theorem main : ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∀ x : EuclideanSpace ℝ ι,
    g x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ) :=
  ⟨gauss ι, gauss_apply ι⟩

end

end WsC.GS

theorem solution (ι : Type) [Fintype ι] :
    ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∀ x : EuclideanSpace ℝ ι,
      g x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ) := by
  exact WsC.GS.main ι

end S_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
end P2MW
export P2MW.S_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (solution)

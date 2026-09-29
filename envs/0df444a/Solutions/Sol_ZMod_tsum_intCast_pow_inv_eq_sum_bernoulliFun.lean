-- Prove2me | solution 1 for ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b4a29729-c6a8-5edb-ab1a-3c4f43d63de6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun

set_option autoImplicit false

open Real Complex
open scoped Nat

namespace CardC0

variable {N : ℕ} [NeZero N] {k : ℕ}

lemma hasSum_twisted (hk : 2 ≤ k) (r : ZMod N) :
    HasSum (fun d : ℤ => ZMod.stdAddChar (r * (d : ZMod N)) * ((d : ℂ) ^ k)⁻¹)
      (-(2 * π * I) ^ k / k ! * (bernoulliFun k ((r.val : ℝ) / N) : ℂ)) := by
  have hx : ((r.val : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by exact_mod_cast NeZero.pos N)]
    exact_mod_cast (ZMod.val_lt r).le
  have h := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx
  refine h.congr_fun fun d => ?_
  rw [fourier_coe_apply, one_div, mul_comm]
  congr 1
  have : (r * (d : ZMod N) : ZMod N) = (((r.val : ℤ) * d : ℤ) : ZMod N) := by
    simp
  rw [this, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

lemma summable_inv_pow (hk : 2 ≤ k) : Summable fun d : ℤ => ((d : ℂ) ^ k)⁻¹ := by
  have : Summable fun d : ℤ => (1 : ℝ) / (d : ℝ) ^ k := Real.summable_one_div_int_pow.mpr (by omega)
  have := (this.map Complex.ofRealCLM Complex.ofRealCLM.continuous)
  refine this.congr fun d => ?_
  simp

lemma norm_stdAddChar (x : ZMod N) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

lemma summable_twisted (hk : 2 ≤ k) (r : ZMod N) :
    Summable fun d : ℤ => ZMod.stdAddChar (r * (d : ZMod N)) * ((d : ℂ) ^ k)⁻¹ := by
  refine Summable.of_norm_bounded (g := fun d : ℤ => ‖((d : ℂ) ^ k)⁻¹‖) (summable_inv_pow hk).norm ?_
  intro d
  rw [norm_mul, norm_stdAddChar, one_mul]

lemma indicator_eq_sum (a b : ZMod N) :
    (if b = a then (1 : ℂ) else 0) =
      (N : ℂ)⁻¹ * ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * ZMod.stdAddChar (r * b) := by
  have h := AddChar.sum_mulShift (b - a) (ZMod.isPrimitive_stdAddChar N)
  simp only [ZMod.card, sub_eq_zero] at h
  have h2 : ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * ZMod.stdAddChar (r * b) =
      ∑ r : ZMod N, ZMod.stdAddChar (r * (b - a)) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [h2, h]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  split_ifs <;> simp [hN]

theorem main (hk : 2 ≤ k) (a : ZMod N) :
    ∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹ =
      -(2 * π * I) ^ k / (k ! * N) *
        ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * (bernoulliFun k ((r.val : ℝ) / N) : ℂ) := by

  have h1 : ∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹ =
      ∑' d : ℤ, (if (d : ZMod N) = a then (1 : ℂ) else 0) * ((d : ℂ) ^ k)⁻¹ := by
    rw [show (∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹) =
        ∑' d : ({d : ℤ | (d : ZMod N) = a} : Set ℤ), ((d : ℂ) ^ k)⁻¹ from rfl,
      tsum_subtype {d : ℤ | (d : ZMod N) = a} (fun d : ℤ => ((d : ℂ) ^ k)⁻¹)]
    refine tsum_congr fun d => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> simp
  rw [h1]

  have h2 : ∀ d : ℤ, (if (d : ZMod N) = a then (1 : ℂ) else 0) * ((d : ℂ) ^ k)⁻¹ =
      ∑ r : ZMod N, ((N : ℂ)⁻¹ * ZMod.stdAddChar (-(r * a))) *
        (ZMod.stdAddChar (r * (d : ZMod N)) * ((d : ℂ) ^ k)⁻¹) := by
    intro d
    rw [indicator_eq_sum a, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp_rw [h2]
  rw [Summable.tsum_finsetSum (fun r _ => (summable_twisted hk r).mul_left _)]
  simp_rw [tsum_mul_left]

  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [(hasSum_twisted hk r).tsum_eq]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

end CardC0

theorem solution (N : ℕ) [NeZero N] (k : ℕ) (hk : 2 ≤ k)
    (a : ZMod N) :
    ∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹ =
      -(2 * π * I) ^ k / (k ! * N) *
        ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * (bernoulliFun k ((r.val : ℝ) / N) : ℂ) :=
  CardC0.main hk a

end S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun
end P2MW
export P2MW.S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun (solution)

-- Prove2me | solution 1 for QuaternionAlgebra.norm_nrd_add_le_max_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c86c4d7c-8c90-5b0e-82f0-50da9346dcf1

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_norm_nrd_add_le_max_of_forall_isUnit

set_option autoImplicit false

open scoped Quaternion

namespace QuatVal

variable {p : ℕ} [Fact p.Prime] {a b : ℚ_[p]}

open QuaternionAlgebra

theorem nrd_mul (x y : ℍ[ℚ_[p], a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem nrd_add (x y : ℍ[ℚ_[p], a, b]) : nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, nrd_mk, trd_mk]
  ring

theorem nrd_smul (c : ℚ_[p]) (x : ℍ[ℚ_[p], a, b]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, nrd_mk, smul_eq_mul]
  ring

theorem nrd_ne_zero_of_isUnit {x : ℍ[ℚ_[p], a, b]} (hx : IsUnit x) : nrd x ≠ 0 := by
  obtain ⟨u, rfl⟩ := hx
  intro h0
  have h1 : nrd ((u : ℍ[ℚ_[p], a, b]) * (↑u⁻¹ : ℍ[ℚ_[p], a, b])) = 1 := by rw [Units.mul_inv, nrd_one]
  rw [nrd_mul, h0, zero_mul] at h1
  exact zero_ne_one h1

theorem norm_nrd_pow (z : ℍ[ℚ_[p], a, b]) (i : ℕ) : ‖nrd (z ^ i)‖ = ‖nrd z‖ ^ i := by
  induction i with
  | zero => rw [pow_zero, nrd_one, norm_one, pow_zero]
  | succ k ih => rw [pow_succ, nrd_mul, norm_mul, ih, pow_succ]

theorem norm_nrd_add_le_one (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    {x y : ℍ[ℚ_[p], a, b]} (hx : ‖nrd x‖ ≤ 1) (hy : ‖nrd y‖ ≤ 1) : ‖nrd (x + y)‖ ≤ 1 := by
  have hxy : ‖nrd (x * star y)‖ ≤ 1 := by
    rw [nrd_mul, nrd_star, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  have htrd := QuaternionAlgebra.norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one p a b hdiv (x * star y) hxy
  rw [nrd_add]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hx hy)) htrd)

theorem norm_nrd_add_le_max (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    (x y : ℍ[ℚ_[p], a, b]) : ‖nrd (x + y)‖ ≤ max ‖nrd x‖ ‖nrd y‖ := by

  wlog hle : ‖nrd x‖ ≤ ‖nrd y‖ generalizing x y
  · rw [add_comm, max_comm]; exact this y x (le_of_not_ge hle)
  rw [max_eq_right hle]
  by_cases hy0 : y = 0
  · subst hy0
    rw [nrd_zero, norm_zero] at hle
    have hx0 : ‖nrd x‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [add_zero, nrd_zero, norm_zero, hx0]
  obtain ⟨u, rfl⟩ := hdiv y hy0
  have hu0 : nrd (u : ℍ[ℚ_[p], a, b]) ≠ 0 := nrd_ne_zero_of_isUnit u.isUnit
  have hnu : ‖nrd (u : ℍ[ℚ_[p], a, b])‖ ≠ 0 := norm_ne_zero_iff.mpr hu0

  have hfac : x + (u : ℍ[ℚ_[p], a, b]) = (u : ℍ[ℚ_[p], a, b]) * ((↑u⁻¹ : ℍ[ℚ_[p], a, b]) * x + 1) := by
    rw [mul_add, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
  have h1 : ‖nrd ((↑u⁻¹ : ℍ[ℚ_[p], a, b]) * x)‖ ≤ 1 := by
    have hinv : nrd (↑u⁻¹ : ℍ[ℚ_[p], a, b]) * nrd (u : ℍ[ℚ_[p], a, b]) = 1 := by
      rw [← nrd_mul, Units.inv_mul, nrd_one]
    rw [nrd_mul, norm_mul]
    have : ‖nrd (↑u⁻¹ : ℍ[ℚ_[p], a, b])‖ = ‖nrd (u : ℍ[ℚ_[p], a, b])‖⁻¹ := by
      rw [← norm_inv]; congr 1; exact eq_inv_of_mul_eq_one_left hinv
    rw [this, inv_mul_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) hnu.symm), mul_one]
    exact hle
  have h2 := norm_nrd_add_le_one hdiv h1 (by rw [nrd_one, norm_one])
  rw [hfac, nrd_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) h2

theorem norm_nrd_le_one_of_isIntegral (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    (z : ℍ[ℚ_[p], a, b]) (hz : IsIntegral ℤ_[p] z) : ‖nrd z‖ ≤ 1 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨f, hf, hfz⟩ := hz

  set n := f.natDegree with hn
  have hsum : z ^ n = -∑ i ∈ Finset.range n, (algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] (f.coeff i)) * z ^ i := by
    have h := hfz
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h

  have hval : ∀ i ∈ Finset.range n, ‖nrd ((algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] (f.coeff i)) * z ^ i)‖ < ‖nrd z‖ ^ n := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [nrd_mul, norm_mul]
    have hc : ‖nrd (algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] (f.coeff i))‖ ≤ 1 := by
      rw [show algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] (f.coeff i) = ((f.coeff i : ℚ_[p]) : ℍ[ℚ_[p], a, b]) from rfl,
        nrd_coe, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one _)
    rw [norm_nrd_pow]
    calc ‖nrd ((algebraMap ℤ_[p] ℍ[ℚ_[p], a, b]) (f.coeff i))‖ * ‖nrd z‖ ^ i ≤ 1 * ‖nrd z‖ ^ i :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg _) _)
      _ = ‖nrd z‖ ^ i := one_mul _
      _ < ‖nrd z‖ ^ n := pow_lt_pow_right₀ hgt hi

  have hult : ∀ (s : Finset ℕ) (g : ℕ → ℍ[ℚ_[p], a, b]) (C : ℝ), 0 ≤ C → (∀ i ∈ s, ‖nrd (g i)‖ < C) → 0 < C →
      ‖nrd (∑ i ∈ s, g i)‖ < C := by
    intro s g C hC0 hg hCpos
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, nrd_zero, norm_zero]; exact hCpos
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      refine lt_of_le_of_lt (norm_nrd_add_le_max hdiv _ _) (max_lt (hg i (Finset.mem_insert_self i s)) ?_)
      exact ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
  have hzn : ‖nrd (z ^ n)‖ = ‖nrd z‖ ^ n := norm_nrd_pow z n
  have hpos : 0 < ‖nrd z‖ ^ n := pow_pos (lt_trans zero_lt_one hgt) n
  have hlt := hult (Finset.range n) _ (‖nrd z‖ ^ n) hpos.le hval hpos
  rw [← nrd_neg, ← hsum, hzn] at hlt
  exact lt_irrefl _ hlt

end QuatVal

theorem solution
    (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    (x y : ℍ[ℚ_[p], a, b]) :
    ‖QuaternionAlgebra.nrd (x + y)‖ ≤ max ‖QuaternionAlgebra.nrd x‖ ‖QuaternionAlgebra.nrd y‖ :=
  QuatVal.norm_nrd_add_le_max hdiv x y

end S_QuaternionAlgebra_norm_nrd_add_le_max_of_forall_isUnit
end P2MW
export P2MW.S_QuaternionAlgebra_norm_nrd_add_le_max_of_forall_isUnit (solution)

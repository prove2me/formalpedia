-- Prove2me | solution 1 for WeierstrassCurve.exists_isIntegralModelOf_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/da518cd8-de84-5c48-b894-36c56fbfe657

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isIntegralModelOf_rat

set_option maxHeartbeats 3200000

open WeierstrassCurve

private lemma den_clears (q : ℚ) {n : ℕ} (h : q.den ∣ n) :
    ∃ m : ℤ, (m : ℚ) = (n : ℚ) * q := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨(k : ℤ) * q.num, ?_⟩
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have key : (q.den : ℚ) * q = (q.num : ℚ) := by
    rw [mul_comm, ← eq_div_iff hd]; exact (Rat.num_div_den q).symm
  push_cast
  rw [mul_comm (q.den : ℚ), mul_assoc, key]

theorem solution (E : WeierstrassCurve ℚ) :
    ∃ W : WeierstrassCurve ℤ, W.IsIntegralModelOf E := by
  set d : ℕ := E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den with hd_def
  have hdq : (d : ℚ) ≠ 0 := by
    rw [hd_def]; push_cast
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (Nat.cast_ne_zero.mpr E.a₁.den_nz) (Nat.cast_ne_zero.mpr E.a₂.den_nz))
      (Nat.cast_ne_zero.mpr E.a₃.den_nz)) (Nat.cast_ne_zero.mpr E.a₄.den_nz))
      (Nat.cast_ne_zero.mpr E.a₆.den_nz)
  have hd1 : E.a₁.den ∣ d :=
    ⟨E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den, by rw [hd_def]; ring⟩
  have hd2 : E.a₂.den ∣ d :=
    ⟨E.a₁.den * E.a₃.den * E.a₄.den * E.a₆.den, by rw [hd_def]; ring⟩
  have hd3 : E.a₃.den ∣ d :=
    ⟨E.a₁.den * E.a₂.den * E.a₄.den * E.a₆.den, by rw [hd_def]; ring⟩
  have hd4 : E.a₄.den ∣ d :=
    ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₆.den, by rw [hd_def]; ring⟩
  have hd6 : E.a₆.den ∣ d :=
    ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den, by rw [hd_def]; ring⟩
  obtain ⟨m₁, hm₁⟩ := den_clears E.a₁ (n := d ^ 1) (hd1.trans (dvd_pow_self d one_ne_zero))
  obtain ⟨m₂, hm₂⟩ := den_clears E.a₂ (n := d ^ 2) (hd2.trans (dvd_pow_self d two_ne_zero))
  obtain ⟨m₃, hm₃⟩ := den_clears E.a₃ (n := d ^ 3) (hd3.trans (dvd_pow_self d three_ne_zero))
  obtain ⟨m₄, hm₄⟩ := den_clears E.a₄ (n := d ^ 4) (hd4.trans (dvd_pow_self d four_ne_zero))
  obtain ⟨m₆, hm₆⟩ := den_clears E.a₆ (n := d ^ 6)
    (hd6.trans (dvd_pow_self d (by norm_num : (6:ℕ) ≠ 0)))
  refine ⟨⟨m₁, m₂, m₃, m₄, m₆⟩, ⟨(Units.mk0 (d : ℚ) hdq)⁻¹, 0, 0, 0⟩, ?_⟩
  ext <;>
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, Int.coe_castRingHom,
               variableChange_a₁, variableChange_a₂, variableChange_a₃,
               variableChange_a₄, variableChange_a₆,
               inv_inv, Units.val_mk0, Units.val_inv_eq_inv_val,
               mul_zero, add_zero, zero_mul, sub_zero, zero_pow, mul_one,
               hm₁, hm₂, hm₃, hm₄, hm₆] <;>
    push_cast <;> ring

end S_WeierstrassCurve_exists_isIntegralModelOf_rat
end P2MW
export P2MW.S_WeierstrassCurve_exists_isIntegralModelOf_rat (solution)

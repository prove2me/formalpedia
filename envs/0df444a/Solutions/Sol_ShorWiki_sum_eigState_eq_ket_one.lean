-- Prove2me | solution 1 for ShorWiki.sum_eigState_eq_ket_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:40:36.976027+00:00
-- url     : https://prove2.me/submissions/70a7fe88-557a-48b9-b81f-90928b187dc5

import Mathlib
import Definitions.Def_ShorWiki_Defs
open ShorWiki

namespace ShorSumEig

lemma inner_sum (r k : ℕ) (hr : 0 < r) (hk : k < r) :
    ∑ j ∈ Finset.range r, (omega r ^ (k * j))⁻¹ = if k = 0 then (r : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (omega r) r := Complex.isPrimitiveRoot_exp r hr.ne'
  split_ifs with hk0
  · subst hk0; simp
  · set x := (omega r)⁻¹ ^ k with hx
    have hprim' := hprim.inv
    have hx1 : x ≠ 1 := by
      intro h
      have := (hprim'.pow_eq_one_iff_dvd k).mp h
      have := Nat.le_of_dvd (by omega) this
      omega
    have hxr : x ^ r = 1 := by
      rw [hx, ← pow_mul, mul_comm, pow_mul, hprim'.pow_eq_one, one_pow]
    have e : ∑ j ∈ Finset.range r, (omega r ^ (k * j))⁻¹ = ∑ j ∈ Finset.range r, x ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx, ← inv_pow, ← pow_mul]
    rw [e]
    have hg := geom_sum_mul x r
    rw [hxr, sub_self] at hg
    rcases mul_eq_zero.mp hg with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hx1

lemma ord_pos (N a : ℕ) (haN : a < N) (hcop : Nat.Coprime a N) : 0 < ord N a := by
  have : NeZero N := ⟨by omega⟩
  unfold ord
  have : orderOf (ZMod.unitOfCoprime a hcop) = orderOf (a : ZMod N) := by
    rw [← orderOf_units]; rfl
  rw [← this]
  exact orderOf_pos _

end ShorSumEig

open ShorSumEig in
theorem solution (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) :
    (1 / Real.sqrt (ord N a) : ℂ) • ∑ j ∈ Finset.range (ord N a), eigState N a (regBits N) j
      = ket (2 ^ regBits N) 1 := by
  set r := ord N a with hr
  have hr0 : 0 < r := ord_pos N a haN hcop
  have hsq : ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = r := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hsq0 : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr (by exact_mod_cast hr0)
    exact_mod_cast this.ne'
  have h1N : 1 % N = 1 := Nat.mod_eq_of_lt (by omega)
  funext i
  simp only [Pi.smul_apply, Finset.sum_apply, eigState, smul_eq_mul, ket]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← hr]
  have hin : ∀ y ∈ Finset.range r, (∑ x ∈ Finset.range r,
      (omega r ^ (y * x))⁻¹ * if (i : ℕ) = a ^ y % N then (1 : ℂ) else 0) =
      (if y = 0 then (r : ℂ) else 0) * if (i : ℕ) = a ^ y % N then (1 : ℂ) else 0 := by
    intro y hy
    rw [← Finset.sum_mul, inner_sum r y hr0 (Finset.mem_range.mp hy)]
  rw [Finset.sum_congr rfl hin]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, if_pos hr0, pow_zero, h1N]
  split_ifs
  · field_simp
    rw [sq, hsq]
  · simp

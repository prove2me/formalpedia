-- Prove2me | solution 1 for P2M_FixedOrderFactor_muAvg_eq__11fccbbf11a9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:18.409728+00:00
-- url     : https://prove2.me/submissions/296eff86-e1d2-4d78-8c3b-80e2cfaf4acb

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
public import Theorems.Thm_FixedOrderFactor_one_sub_mul_ne_zero
public import Theorems.Thm_FixedOrderFactor_sum_inv_one_sub
public import Theorems.Thm_FixedOrderFactor_conj_rootOfUnity
public import Theorems.Thm_FixedOrderFactor_localTerm_complex
public import Theorems.Thm_FixedOrderFactor_partial_fraction

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) {x : ℝ} (hx : |x| < 1) :
    muAvg r x = (1 + x ^ r) / ((1 - x ^ 2) * (1 - x ^ r)) := by
  have hxr : |x| ^ r < 1 := pow_lt_one₀ (abs_nonneg x) hx hr.ne'
  have hxr' : x ^ r ≠ 1 := by
    intro h; rw [← abs_pow, h] at hxr; simp at hxr
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have : |x| ^ 2 = 1 := by rw [sq_abs, h]
    nlinarith [abs_nonneg x]
  have hxrC : (x : ℂ) ^ r ≠ 1 := by exact_mod_cast hxr'
  have h1 : (1 : ℝ) - x ^ r ≠ 0 := sub_ne_zero.mpr (Ne.symm hxr')
  have h2 : (1 : ℝ) - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx2)
  apply Complex.ofReal_injective
  have hsum1 := sum_inv_one_sub hr hxrC
  have hsum2 : ∑ j ∈ range r, 1 / (1 - (starRingEnd ℂ) (rootOfUnity r j) * x) =
      r / (1 - (x : ℂ) ^ r) := by
    have := congrArg (starRingEnd ℂ) hsum1
    simpa [map_sum, map_div₀, map_sub, Complex.conj_ofReal] using this
  have hterm : ∀ j ∈ range r, (localTerm (rootOfUnity r j) x : ℂ) =
      (1 / (1 - (x : ℂ) ^ 2)) * (1 / (1 - rootOfUnity r j * x) +
        1 / (1 - (starRingEnd ℂ) (rootOfUnity r j) * x) - 1) := by
    intro j _
    have hc := conj_rootOfUnity r j
    rw [localTerm_complex _ hc]
    have ha := one_sub_mul_ne_zero hr j hxrC
    have hb : 1 - (starRingEnd ℂ) (rootOfUnity r j) * x ≠ 0 := by
      intro h
      apply ha
      have h' : (starRingEnd ℂ) (1 - (starRingEnd ℂ) (rootOfUnity r j) * x) = 0 := by
        rw [h, map_zero]
      simpa [map_sub, Complex.conj_ofReal] using h'
    exact partial_fraction ha hb (by linear_combination (x : ℂ) ^ 2 * hc) (by exact_mod_cast h2)
  rw [muAvg, Complex.ofReal_mul, Complex.ofReal_sum, sum_congr rfl hterm, ← mul_sum,
    sum_sub_distrib, sum_add_distrib, hsum1, hsum2]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1C : (1 : ℂ) - (x : ℂ) ^ r ≠ 0 := by exact_mod_cast h1
  have h2C : (1 : ℂ) - (x : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h2
  push_cast
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  field_simp
  ring
end FixedOrderFactor

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exists_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:16.629294+00:00
-- url     : https://prove2.me/submissions/8ed8f967-61ba-497e-b075-81d8ac0f6822

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExistsCyclic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_sign_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
private theorem sum_pow_mul_inv_prod_sub_eq_ite {m : ℕ} (x : Fin m → ℝ) (hx : Function.Injective x) (k : ℕ)
    (hk : k < m) :
    ∑ s : Fin m, x s ^ k * (∏ j ∈ univ.erase s, (x s - x j))⁻¹ = if k + 1 = m then 1 else 0 := by
  classical
  have hinj : Set.InjOn x ((univ : Finset (Fin m)) : Set (Fin m)) := fun a _ b _ h => hx h
  have hdeg : (Polynomial.X ^ k : Polynomial ℝ).degree < ((univ : Finset (Fin m)).card : WithBot ℕ) := by
    rw [card_univ, Fintype.card_fin, Polynomial.degree_X_pow]
    exact_mod_cast hk
  have hI := Lagrange.eq_interpolate hinj hdeg
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (m - 1)) hI
  try simp only at hc
  rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff] at hc
  have hb : ∀ s : Fin m, (Lagrange.basis univ x s).coeff (m - 1) =
      (∏ j ∈ univ.erase s, (x s - x j))⁻¹ := by
    intro s
    simp only [Lagrange.basis, Lagrange.basisDivisor]
    rw [Finset.prod_mul_distrib, ← map_prod, Polynomial.coeff_C_mul]
    have hmon : (∏ j ∈ univ.erase s, (Polynomial.X - Polynomial.C (x j))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
    have hnd : (∏ j ∈ univ.erase s, (Polynomial.X - Polynomial.C (x j))).natDegree = m - 1 := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _]
      simp [Polynomial.natDegree_X_sub_C, card_erase_of_mem]
    rw [← hnd, hmon.coeff_natDegree, mul_one, prod_inv_distrib]
  simp only [Polynomial.coeff_C_mul, hb, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow] at hc
  have e : (m - 1 = k) ↔ (k + 1 = m) := by omega
  simp only [e] at hc
  exact hc.symm
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
end

set_option autoImplicit false
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (r : ℕ) (x : Fin (2 * r + 1) → ℝ) (hx : StrictAnti x) :
    ∃ c : Fin (2 * r + 1) → ℝ, (∀ s, c s ≠ 0) ∧ ∀ i j : ℕ, i + j ≤ 2 * r →
      formV (fun s => x s ^ i * c s) (fun s => x s ^ j * c s) = if i + j = 2 * r then -1 else 0 := by
  classical
  have hP : ∀ s, 0 < (-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j) := fun s => sign_prod x hx s
  have hPne : ∀ s, ∏ j ∈ univ.erase s, (x s - x j) ≠ 0 := fun s h => by
    have h1 := hP s
    rw [h, mul_zero] at h1
    exact lt_irrefl _ h1
  have hq : ∀ s, 0 < (-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j) := fun s => by
    have h1 : (-1 : ℝ) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j) =
        ((-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j)) / (∏ j ∈ univ.erase s, (x s - x j)) ^ 2 := by
      have := hPne s
      first
      | (field_simp; done)
      | (field_simp; ring)
    rw [h1]
    exact div_pos (hP s) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hPne s))))
  refine ⟨fun s => Real.sqrt ((-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j)),
    fun s => (Real.sqrt_pos.2 (hq s)).ne', fun i j hij => ?_⟩
  have hterm : ∀ s : Fin (2 * r + 1),
      (-1 : ℝ) ^ (s.val + 1) * (x s ^ i * Real.sqrt ((-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j))) *
        (x s ^ j * Real.sqrt ((-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j))) =
      -(x s ^ (i + j) * (∏ j ∈ univ.erase s, (x s - x j))⁻¹) := by
    intro s
    have hs := Real.mul_self_sqrt (hq s).le
    have hne := hPne s
    rcases Nat.even_or_odd s.val with he | ho
    · rw [he.neg_one_pow] at hs
      rw [he.neg_one_pow, (he.add_one).neg_one_pow, pow_add]
      linear_combination (-(x s ^ i * x s ^ j)) * hs
    · rw [ho.neg_one_pow] at hs
      rw [ho.neg_one_pow, (ho.add_one).neg_one_pow, pow_add]
      linear_combination (x s ^ i * x s ^ j) * hs
  simp only [formV]
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_neg_distrib,
    sum_pow_mul_inv_prod_sub_eq_ite x hx.injective (i + j) (by omega)]
  by_cases h : i + j = 2 * r
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), neg_zero]
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

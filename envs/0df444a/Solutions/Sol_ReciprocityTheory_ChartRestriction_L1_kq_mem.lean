-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kq_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:14.524322+00:00
-- url     : https://prove2.me/submissions/5939a719-eff3-4a38-a65e-95e947e0eba4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_norm_l_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_add_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_add_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_int_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_int_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_sqrtNeg_pow_prime_sq_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_complete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_root
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tch_mem_kur
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tch_near
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tch_norm_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
variable {l}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (d : ℕ) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (δ : ℂ_[l]) (hδ : δ ^ 2 = -(d : ℂ_[l]))
    (hn : ‖δ‖ = 1) : δ ∈ MaximalUnramifiedExtension l := by
  obtain ⟨ξ, hξ, hξδ⟩ := tch_near l δ hn.le 2 (by norm_num) ‖(l : ℂ_[l])‖ (kq_norm_l_lt l)
    (norm_sqrtNeg_pow_prime_sq_sub d hl hld hin δ hδ hn)
  have hlt : ‖δ - ξ‖ < 1 := hξδ.trans_lt (kq_norm_l_lt l)
  have hξ1 : ‖ξ‖ = 1 := by
    refine le_antisymm (tch_norm_le l hξ) (not_lt.mp fun h => ?_)
    have : ‖(δ - ξ) + ξ‖ < 1 := kq_add_lt l _ _ 1 hlt h
    rw [sub_add_cancel, hn] at this
    exact lt_irrefl _ this
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := kq_int_unit l 2 (by
      intro h
      have h' : l ∣ 2 := by exact_mod_cast h
      exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'))
    simpa using this
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  let x₀ : MaximalUnramifiedExtension l := ⟨ξ, tch_mem_kur l hξ⟩
  let P : Polynomial (MaximalUnramifiedExtension l) := Polynomial.X ^ 2 + Polynomial.C (d : MaximalUnramifiedExtension l)
  have hev : ((P.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l]) = (ξ - δ) * (ξ + δ) := by
    have : (ξ - δ) * (ξ + δ) = ξ ^ 2 - δ ^ 2 := by ring
    rw [this, hδ]
    simp [P, x₀]
  have hdv : ((P.derivative.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l]) = 2 * ξ := by
    simp [P, x₀]
    left; norm_num
  have hd1 : ‖(d : ℂ_[l])‖ ≤ 1 := by simpa using kq_int_le l (d : ℤ)
  obtain ⟨x, hx, -⟩ := newton_root P
    (by
      intro i
      change ‖((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ 1
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      by_cases h2i : i = 2
      · subst h2i; simp
      · by_cases h0 : i = 0
        · subst h0; simpa using hd1
        · simp [h2i, h0])
    x₀ hξ1.le
    (by
      change ‖((P.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1
      rw [hev, norm_mul, norm_sub_rev]
      have : ‖ξ + δ‖ ≤ 1 := kq_add_le l _ _ 1 hξ1.le hn.le
      exact (mul_le_of_le_one_right (norm_nonneg _) this).trans_lt hlt)
    (by
      change ‖((P.derivative.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1
      rw [hdv, norm_mul, h2, hξ1, one_mul])
  have hx' : (x : ℂ_[l]) ^ 2 = δ ^ 2 := by
    have : ((P.eval x : MaximalUnramifiedExtension l) : ℂ_[l]) = 0 := by rw [hx]; rfl
    simp only [P, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at this
    push_cast at this
    rw [hδ]
    linear_combination this
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx' with h | h
  · rw [← h]; exact x.2
  · have : δ = -(x : ℂ_[l]) := by rw [h, neg_neg]
    rw [this]; exact neg_mem x.2
end ReciprocityTheory.ChartRestriction.L1

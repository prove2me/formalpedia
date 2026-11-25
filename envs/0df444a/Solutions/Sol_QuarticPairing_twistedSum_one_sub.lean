-- Prove2me | solution 1 for QuarticPairing.twistedSum_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:40:43.191208+00:00
-- url     : https://prove2.me/submissions/43b1a979-372b-422c-a37d-fadbbb92e38e

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_norm_unitDir_le
public import Theorems.Thm_QuarticPairing_term_one_add

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
open Classical
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    ‖twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ ≤
      2 * defectSum g Λ β E X := by
  unfold twistedSum defectSum
  set s := (normBall X).filter (fun c => (4 : GaussianInt) ∣ c - β)
  rw [map_sum, mul_sum, ← sum_add_distrib, ← sum_filter_add_sum_filter_not s E]
  rw [sum_eq_zero (s := s.filter fun c => ¬ E c) (fun c hc =>
    term_one_add (g c) κ hκ c (Λ c) (h12 c (mem_filter.1 hc).2)), add_zero, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_conj, zpow_one, zpow_zero, mul_one,
    Complex.norm_real, Real.norm_eq_abs, hκ, one_mul]
  have h1 := norm_unitDir_le c
  have h2 : 0 ≤ ‖g c‖ := norm_nonneg _
  have h3 : 0 ≤ |Λ c| := abs_nonneg _
  nlinarith [mul_nonneg h2 h3, mul_le_mul_of_nonneg_left h1 h2]
end QuarticPairing

-- Prove2me | solution 1 for PI.Tr.gaussStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:59.829285+00:00
-- url     : https://prove2.me/submissions/5a37f2b2-9d69-46f6-9ea0-88837b185c09

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_GaussAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_NumericMain
import Theorems.Thm_PI_Tr_numeric_main
import Theorems.Thm_PI_Tr_factor_le
import Theorems.Thm_PI_Tr_gauss_abstract


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped Real
open PI PI.Tr
namespace PI.Tr
theorem _root_.solution : GaussStep := by
  intro hP E _ _ _ Λ _ _ lam u hn hlam hdual
  obtain ⟨sA, sQ, c, hc, PE⟩ := hP E Λ
  by_contra hcon
  push_neg at hcon
  set n : ℝ := (finrank ℝ E : ℝ) with hndef
  have hn2 : (2 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  set m : ℝ := n / 2 with hmdef
  have hm1 : 1 ≤ m := by rw [hmdef]; linarith
  have hm0 : 0 < m := by linarith
  set R2 : ℝ := (m / lam) ^ 2 with hR2
  set s : ℝ := 18 / 25 * lam ^ 2 / m with hsdef
  have hs : 0 < s := by positivity
  have hR : ∀ x : Λ, R2 ≤ ‖(x : E) + -u‖ ^ 2 := by
    intro x
    have h := hcon x x.2
    have h' : m / lam < ‖(x : E) + -u‖ := by
      rw [div_lt_iff₀ hlam, ← sub_eq_add_neg, norm_sub_rev]
      rw [hmdef]; linarith
    rw [hR2]
    exact pow_le_pow_left₀ (by positivity) h'.le 2
  have hl : ∀ y : dualLat Λ, ‖(y : E)‖ ^ 2 < lam ^ 2 →
      Real.cos (2 * π * inner ℝ (y : E) (-u)) = 1 := by
    intro y hy
    have hy' : ‖(y : E)‖ < lam := by
      nlinarith [norm_nonneg (y : E)]
    obtain ⟨k, hk⟩ := hdual y (fun x hx => y.2 x hx) hy'
    rw [inner_neg_right, real_inner_comm, hk]
    have : 2 * π * -(k : ℝ) = ((-k : ℤ) : ℝ) * (2 * π) := by push_cast; ring
    rw [this, Real.cos_int_mul_two_pi]
  have key := gauss_abstract (X := Λ) (Y := dualLat Λ) (fun x => ‖(x : E) + -u‖ ^ 2)
    (fun x => ‖(x : E) + 0‖ ^ 2) (fun y => ‖(y : E)‖ ^ 2)
    (fun y => Real.cos (2 * π * inner ℝ (y : E) (-u))) n c
    (fun y => sq_nonneg _) (fun x => sq_nonneg _) (fun y => Real.abs_cos_le_one _) hc 0
    (fun t ht => sA t ht (-u)) (fun t ht => sA t ht 0) (fun t ht => sQ t ht)
    (fun t ht => PE t ht (-u))
    (fun t ht => by
      rw [PE t ht 0]
      simp only [inner_zero_right, mul_zero, Real.cos_zero, mul_one])
    R2 (lam ^ 2) hR hl s (4 / 9) (1 / 4) hs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hm0' : m ≠ 0 := hm0.ne'
  have e1 : -π * s * (1 - 4 / 9) * R2 = -(2 * π / 5) * m := by
    rw [hsdef, hR2]; field_simp; ring
  have e2 : -π * (1 - 1 / 4) * lam ^ 2 / s = -(25 * π / 24) * m := by
    rw [hsdef]; field_simp; ring
  have e3 : -n / 2 = -m := by rw [hmdef]; ring
  rw [e1, e2, e3] at key
  have hN := numeric_main
  have hA : 0 < Real.exp (-(2 * π / 5)) := Real.exp_pos _
  have hB : 0 < Real.exp (-(25 * π / 24)) := Real.exp_pos _
  have f1 := factor_le (2 * π / 5) (4 / 9) m (by norm_num) hm1 (by
    rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]; linarith)
  have f2 := factor_le (25 * π / 24) (1 / 4) m (by norm_num) hm1 (by
    rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]; linarith)
  rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num] at f1
  rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at f2
  linarith
end PI.Tr

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.cmPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:45:53.699989+00:00
-- url     : https://prove2.me/submissions/a16b0e42-d695-42a2-ad9a-126d946a9c9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModCMPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_omegaK_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_omegaK_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {d : ℕ} (hd : 0 < d) {L : PeriodPair} (hL : HasCMBy d L) {c : ℂ} {τ : ℍ}
    (h : IsTauOf L c τ) (x y : ℤ) :
    ∃ A B C D : ℤ, ((x : ℂ) + y * omegaK d) * τ = A * τ + B ∧ (x : ℂ) + y * omegaK d = C * τ + D ∧
      4 * (A * D - B * C) = 4 * x ^ 2 + 4 * x * y + y ^ 2 * (1 + d) := by
  obtain ⟨hc, hmem⟩ := h
  have hmul : ∀ w ∈ L.lattice, ((x : ℂ) + y * omegaK d) * w ∈ L.lattice := by
    intro w hw
    have h1 : (x : ℂ) * w ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem hw x
    have h2 : (y : ℂ) * (omegaK d * w) ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem (hL w hw) y
    have e : ((x : ℂ) + y * omegaK d) * w = (x : ℂ) * w + (y : ℂ) * (omegaK d * w) := by ring
    rw [e]
    exact add_mem h1 h2
  have hcτ : c * (τ : ℂ) ∈ L.lattice := (hmem _).2 ⟨1, 0, by push_cast; ring⟩
  have hc1 : c ∈ L.lattice := (hmem _).2 ⟨0, 1, by push_cast; ring⟩
  obtain ⟨A, B, hAB⟩ := (hmem _).1 (hmul _ hcτ)
  obtain ⟨C, D, hCD⟩ := (hmem _).1 (hmul _ hc1)
  have e1 : ((x : ℂ) + y * omegaK d) * τ = A * τ + B := by
    apply mul_left_cancel₀ hc
    linear_combination hAB
  have e2 : (x : ℂ) + y * omegaK d = C * τ + D := by
    apply mul_left_cancel₀ hc
    linear_combination hCD
  refine ⟨A, B, C, D, e1, e2, ?_⟩

  have key : ((x : ℂ) + y * omegaK d - A) * ((x : ℂ) + y * omegaK d - D) = B * C := by
    linear_combination ((x : ℂ) + y * omegaK d - A) * e2 + (C : ℂ) * e1
  have hω := omegaK_sq d
  obtain ⟨ht, hn⟩ := omegaK_lin hd (t := 8 * x * y + 4 * y ^ 2 - 4 * (A + D) * y)
    (n := 4 * x ^ 2 - y ^ 2 * (1 + d) - 4 * (A + D) * x + 4 * (A * D - B * C)) (by
      push_cast
      linear_combination 4 * key - (y : ℂ) ^ 2 * hω)
  by_cases hy : y = 0
  · subst hy
    simp only [Int.cast_zero, zero_mul, add_zero] at e1 e2
    have hτ : 0 < (τ : ℂ).im := τ.im_pos
    have e2' : (x : ℂ) - D = (C : ℂ) * τ := by linear_combination e2
    have e1' : ((x : ℂ) - A) * τ = (B : ℂ) := by linear_combination e1
    have hC : C = 0 := by
      have := congrArg Complex.im e2'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re] at this
      have h0 : (C : ℝ) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 hτ.ne'
    have hA : A = x := by
      have := congrArg Complex.im e1'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
        Complex.sub_re] at this
      have h0 : ((x : ℝ) - A) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · have : (A : ℝ) = x := by linarith
        exact_mod_cast this
      · exact absurd h0 hτ.ne'
    subst hC hA
    have hD : D = A := by
      have : ((A : ℤ) : ℂ) = D := by linear_combination e2'
      exact_mod_cast this.symm
    subst hD
    ring
  · have h4 : 4 * (y * (2 * x + y - (A + D))) = 0 := by linear_combination ht
    have hs : 2 * x + y - (A + D) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left (by norm_num))).resolve_left hy
    linear_combination hn - 4 * x * hs
end ReciprocityTheory.ChartRestriction.L1

-- Prove2me | solution 1 for StrongConv.cNorm_le_two_mul_sSup_of_subset_add
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:42:30.010299+00:00
-- url     : https://prove2.me/submissions/0b0ae4de-dd1b-48f8-b2e9-e2b710a7ae8a

import Definitions.Def_StrongConv
import Theorems.Thm_markov_inequality_interval
import Mathlib

section
section
open Polynomial
open scoped Pointwise

namespace StrongConv.CitedL42

theorem cNorm_zero_eq (F : ℝ → ℝ) (a : ℝ) :
    cNorm 0 F 0 a = sSup ((fun x => |F x|) '' Set.Icc 0 a) := by
  simp [cNorm, supOn]

theorem main (q : ℕ) (h : ℝ[X]) (hh : h.natDegree ≤ q) (a : ℝ)
    (ha : 0 < a) (I : Set ℝ) (hI : I ⊆ Set.Icc 0 a)
    (hdense : Set.Icc 0 a ⊆ I + Set.Icc (-(a / (4 * (q : ℝ) ^ 2))) (a / (4 * (q : ℝ) ^ 2))) :
    cNorm 0 (fun x => h.eval x) 0 a ≤ 2 * sSup ((fun x => |h.eval x|) '' I) := by
  rw [cNorm_zero_eq]
  have hcont : Continuous (fun x => |h.eval x|) := (Polynomial.continuous h).abs
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 ha.le)
    hcont.continuousOn
  set M := |h.eval x0| with hM
  have hsup : sSup ((fun x => |h.eval x|) '' Set.Icc 0 a) = M := by
    apply le_antisymm
    · apply csSup_le (Set.Nonempty.image _ (Set.nonempty_Icc.2 ha.le))
      rintro _ ⟨x, hx, rfl⟩; exact hmax hx
    · exact le_csSup (isCompact_Icc.image hcont).bddAbove ⟨x0, hx0, rfl⟩
  rw [hsup]
  have hbound : ∀ x : ℝ, 0 ≤ x → x ≤ a → |h.eval x| ≤ M := fun x h1 h2 => hmax ⟨h1, h2⟩
  have hM0 : 0 ≤ M := abs_nonneg _
  obtain ⟨y, hy, t, ht, hyt⟩ := hdense hx0
  have hyI := hI hy
  set δ := a / (4 * (q : ℝ) ^ 2) with hδ
  have hdiff : |h.eval x0 - h.eval y| ≤ M / 2 := by
    have hderiv : ∀ c ∈ Set.uIcc y x0, |h.derivative.eval c| ≤ 2 * (q : ℝ) ^ 2 * M / (a - 0) := by
      intro c hc
      have hc' : c ∈ Set.Icc 0 a := Set.uIcc_subset_Icc hyI hx0 hc
      exact markov_inequality_interval 0 a ha h M hh (fun x h1 h2 => hbound x h1 h2) c hc'.1 hc'.2
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := fun x => h.eval x)
      (C := 2 * (q : ℝ) ^ 2 * M / (a - 0)) (s := Set.uIcc y x0)
      (fun x _ => (Polynomial.differentiable h).differentiableAt)
      (fun x hx => by
        rw [Polynomial.deriv, Real.norm_eq_abs]; exact hderiv x hx)
      (convex_uIcc y x0) Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [Real.norm_eq_abs] at hmvt
    have hxy : |x0 - y| ≤ δ := by
      rw [← hyt]; simp only [add_sub_cancel_left]; exact abs_le.2 ⟨ht.1, ht.2⟩
    calc |h.eval x0 - h.eval y| ≤ 2 * (q : ℝ) ^ 2 * M / (a - 0) * |x0 - y| := hmvt
      _ ≤ 2 * (q : ℝ) ^ 2 * M / (a - 0) * δ := by
          apply mul_le_mul_of_nonneg_left hxy; rw [sub_zero]; positivity
      _ ≤ M / 2 := by
          rw [sub_zero, hδ]
          rcases Nat.eq_zero_or_pos q with hq | hq
          · subst hq; simp; positivity
          · have hq' : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
            apply le_of_eq; field_simp; ring
  have hyb : |h.eval y| ≤ sSup ((fun x => |h.eval x|) '' I) := by
    refine le_csSup ?_ ⟨y, hy, rfl⟩
    exact ((isCompact_Icc.image hcont).bddAbove).mono (Set.image_mono hI)
  have : M ≤ |h.eval y| + M / 2 := by
    have := abs_sub_abs_le_abs_sub (h.eval x0) (h.eval y)
    linarith
  linarith

end StrongConv.CitedL42

alias StrongConv.cNorm_le_two_mul_sSup_of_subset_add_dev := StrongConv.CitedL42.main

end
end

section
open Polynomial
open scoped Pointwise
open StrongConv

theorem solution (q : ℕ) (h : ℝ[X]) (hh : h.natDegree ≤ q) (a : ℝ)
    (ha : 0 < a) (I : Set ℝ) (hI : I ⊆ Set.Icc 0 a)
    (hdense : Set.Icc 0 a ⊆ I + Set.Icc (-(a / (4 * (q : ℝ) ^ 2))) (a / (4 * (q : ℝ) ^ 2))) :
    cNorm 0 (fun x => h.eval x) 0 a ≤ 2 * sSup ((fun x => |h.eval x|) '' I) := by
  apply StrongConv.cNorm_le_two_mul_sSup_of_subset_add_dev <;> assumption

end

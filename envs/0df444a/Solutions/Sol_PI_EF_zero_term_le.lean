-- Prove2me | solution 1 for PI.EF.zero_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:10:50.725171+00:00
-- url     : https://prove2.me/submissions/1aa25639-7776-4adb-ac9a-b970be0727a3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Theorems.Thm_PI_EF_norm_sub_ctr_sq
import Theorems.Thm_PI_EF_DZ_facts
import Theorems.Thm_PI_EF_Lent_eq_zero_iff
import Theorems.Thm_PI_EF_ctr_im
import Theorems.Thm_PI_EF_ctr_re
import Theorems.Thm_PI_EF_mult_zero_of_even
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.EF.ctr_im
attribute [local simp] PI.EF.ctr_re



set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ}
    (s : ℂ) (hs : s.im = t) :
    ‖(open Classical in if (0 : ℂ) ∈ DZ χ t then (mult χ 0 : ℂ) / (s - 0) else 0) - eps0 χ / s‖
      ≤ 1 := by
  classical
  by_cases h0 : (0 : ℂ) ∈ DZ χ t
  · obtain ⟨-, hL, -, h⟩ := DZ_facts hZL hχ h0
    rcases h with h | h
    · simp at h
    · obtain ⟨-, he, h1⟩ := h
      have hm := (mult_zero_of_even hχ he h1).2
      simp only [h0, if_true, mult, hm, eps0, he, h1, ne_eq, not_false_eq_true, and_self, sub_zero]
      simp
  · simp only [h0, if_false, zero_sub, norm_neg]
    unfold eps0
    split_ifs with he
    · have hL := (mult_zero_of_even hχ he.1 he.2).1
      have h0' : ¬ ((0 : ℂ) ∈ closedBall (ctr t) (11 / 4)) := by
        intro hb
        exact h0 ⟨hb, (Lent_eq_zero_iff χ (by norm_num)).2 hL⟩
      rw [mem_closedBall, dist_eq_norm, not_le, zero_sub] at h0'
      have h1 := norm_sub_ctr_sq 0 t
      simp only [zero_re, zero_im, zero_sub] at h1
      have h2 : 1 < t ^ 2 := by nlinarith [norm_nonneg (-ctr t)]
      have h3 : 1 ≤ ‖s‖ := by
        have h4 := Complex.abs_im_le_norm s
        rw [hs] at h4
        have h5 : 1 < |t| := by
          by_contra h6
          have := abs_le.1 (not_lt.1 h6)
          nlinarith
        linarith
      rw [norm_div, norm_one]
      exact div_le_one_of_le₀ h3 (norm_nonneg _)
    · simp
end PI.EF

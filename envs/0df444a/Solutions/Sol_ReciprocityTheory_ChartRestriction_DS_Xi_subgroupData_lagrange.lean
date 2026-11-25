-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.lagrange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:26.63828+00:00
-- url     : https://prove2.me/submissions/4e854774-bb43-4eca-b412-dcd5c4ca154c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_term_bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
namespace ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
theorem _root_.solution (c : Fin 3 → ℂ) {t1 t2 t3 g la : ℝ} (hg : 0 < g) (h1 : 1 ≤ t1) (h3 : t3 ≤ 2)
    (h12 : g ≤ t2 - t1) (h23 : g ≤ t3 - t2)
    (p1 : ‖qv c t1‖ ≤ la) (p2 : ‖qv c t2‖ ≤ la) (p3 : ‖qv c t3‖ ≤ la) :
    ‖c‖ ≤ 12 * la / g ^ 2 := by
  have hla : 0 ≤ la := (norm_nonneg _).trans p1
  have d1 : g ^ 2 ≤ |(t1 - t2) * (t1 - t3)| := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have d2 : g ^ 2 ≤ |(t2 - t1) * (t2 - t3)| := by
    rw [abs_of_nonpos (by nlinarith)]; nlinarith
  have d3 : g ^ 2 ≤ |(t3 - t1) * (t3 - t2)| := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hg2 : 0 < g ^ 2 := by positivity
  have n1 : ((t1 - t2) * (t1 - t3) : ℂ) ≠ 0 := by
    have : (t1 - t2) * (t1 - t3) ≠ 0 := by intro h; rw [h, abs_zero] at d1; linarith
    exact_mod_cast this
  have n2 : ((t2 - t1) * (t2 - t3) : ℂ) ≠ 0 := by
    have : (t2 - t1) * (t2 - t3) ≠ 0 := by intro h; rw [h, abs_zero] at d2; linarith
    exact_mod_cast this
  have n3 : ((t3 - t1) * (t3 - t2) : ℂ) ≠ 0 := by
    have : (t3 - t1) * (t3 - t2) ≠ 0 := by intro h; rw [h, abs_zero] at d3; linarith
    exact_mod_cast this
  have a12 : (t1 : ℂ) - t2 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a13 : (t1 : ℂ) - t3 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a23 : (t2 : ℂ) - t3 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a21 : (t2 : ℂ) - t1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a31 : (t3 : ℂ) - t1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a32 : (t3 : ℂ) - t2 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have key : ∀ (w1 w2 w3 : ℝ), |w1| ≤ 4 → |w2| ≤ 4 → |w3| ≤ 4 →
      ‖qv c t1 * (w1 : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ) + qv c t2 * (w2 : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * (w3 : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ)‖ ≤ 12 * la / g ^ 2 := by
    intro w1 w2 w3 hw1 hw2 hw3
    refine (norm_add₃_le).trans ?_
    have := term_bd p1 hw1 hg2 d1
    have := term_bd p2 hw2 hg2 d2
    have := term_bd p3 hw3 hg2 d3
    have e : 12 * la / g ^ 2 = la * 4 / g ^ 2 + la * 4 / g ^ 2 + la * 4 / g ^ 2 := by ring
    linarith
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · have := key (t2 * t3) (t1 * t3) (t1 * t2) (by rw [abs_of_nonneg (by nlinarith)]; nlinarith)
      (by rw [abs_of_nonneg (by nlinarith)]; nlinarith) (by rw [abs_of_nonneg (by nlinarith)]; nlinarith)
    have e : c 0 = qv c t1 * ((t2 * t3 : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((t1 * t3 : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((t1 * t2 : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 0‖ ≤ _
    rw [e]; exact this
  · have := key (-(t2 + t3)) (-(t1 + t3)) (-(t1 + t2)) (by rw [abs_le]; constructor <;> nlinarith)
      (by rw [abs_le]; constructor <;> nlinarith) (by rw [abs_le]; constructor <;> nlinarith)
    have e : c 1 = qv c t1 * ((-(t2 + t3) : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((-(t1 + t3) : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((-(t1 + t2) : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 1‖ ≤ _
    rw [e]; exact this
  · have := key 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    have e : c 2 = qv c t1 * ((1 : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((1 : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((1 : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 2‖ ≤ _
    rw [e]; exact this
end ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData

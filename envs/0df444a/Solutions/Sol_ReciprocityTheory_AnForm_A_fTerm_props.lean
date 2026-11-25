-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fTerm_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:22.976598+00:00
-- url     : https://prove2.me/submissions/3f87cf36-6328-478b-add9-5cdcabdc2072

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedCof_one_diag
import Theorems.Thm_ReciprocityTheory_AnForm_A_re_hessC_diag
import Theorems.Thm_ReciprocityTheory_AnForm_A_greenCoord_thm
import Theorems.Thm_ReciprocityTheory_AnForm_A_greenMixed_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ} (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (j k : Fin (n + 1)) :
    Integrable (fTerm i h j k) ∧ ∫ z, fTerm i h j k z =
      if j = i ∧ k = i then
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w)
      else 0 := by
  have hG := greenCoord_thm n i h hh hhc
  by_cases hjk : j = i ∧ k = i
  · obtain ⟨hj, hk⟩ := hjk
    rw [hj, hk]
    have e : ∀ z, fTerm i h i i z =
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * (Real.log ‖z i‖ * ddcCoordDens i h z) := by
      intro z
      simp only [fTerm, mixedCof_one_diag, Complex.re_ofReal_mul, Complex.re_mul_ofReal,
        re_hessC_diag, ddcCoordDens]
      field_simp
    have e' : fTerm i h i i = fun z =>
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * (Real.log ‖z i‖ * ddcCoordDens i h z) := funext e
    rw [e', if_pos ⟨rfl, rfl⟩, integral_const_mul, hG.2]
    exact ⟨hG.1.const_mul _, rfl⟩
  · have hne : (j, k) ≠ (i, i) := fun h' => hjk ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩
    have hm := greenMixed_thm n i j k h hh hhc hne
    set M := mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) j k
    have hi : Integrable (fun z : Fin (n + 1) → ℂ =>
        (Real.log ‖z i‖ : ℂ) * (hessC h z j k * M)) := by
      simpa [mul_assoc] using hm.1.mul_const M
    refine ⟨Complex.reCLM.integrable_comp hi, ?_⟩
    rw [if_neg hjk]
    have := Complex.reCLM.integral_comp_comm hi
    simp only [Complex.reCLM_apply] at this
    simp only [fTerm]
    rw [this]
    simp_rw [← mul_assoc]
    rw [integral_mul_const, hm.2]
    simp
end ReciprocityTheory.AnForm.A

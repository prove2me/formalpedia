-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_log_maDens_psiRef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:37.066597+00:00
-- url     : https://prove2.me/submissions/8e51ccfc-c70a-4dcd-9b35-30ccd1fe52fa

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_psiRef
import Theorems.Thm_ReciprocityTheory_AnForm_A_fTerm_props

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
theorem _root_.solution (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ}
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    ∫ z, Real.log ‖z i‖ * maDens (Fin.cons h (psiRef n)) z =
      kDens n * ((Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w)) := by
  classical
  have hsplit : (fun z => Real.log ‖z i‖ * maDens (Fin.cons h (psiRef n)) z) =
      fun z => kDens n * ∑ j, ∑ k, fTerm i h j k z := by
    funext z
    rw [maDens_cons_psiRef, Complex.re_sum]
    simp only [fTerm, Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ j, ∫ z, ∑ k, fTerm i h j k z = ∑ k, ∫ z, fTerm i h j k z := fun j =>
    integral_finset_sum _ fun k _ => (fTerm_props i hh hhc j k).1
  have hval : ∀ j k, ∫ z, fTerm i h j k z = if j = i ∧ k = i then
      (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w) else 0 :=
    fun j k => (fTerm_props i hh hhc j k).2
  rw [hsplit, integral_const_mul, integral_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => (fTerm_props i hh hhc j k).1]
  simp only [hint, hval]
  simp [ite_and]
end ReciprocityTheory.AnForm.A

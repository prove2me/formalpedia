-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.leviC_smul_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:23.043262+00:00
-- url     : https://prove2.me/submissions/73904653-b442-4fe8-bd7c-1fee3a2ababb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {e : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin e → ℂ) :
    leviC H a (c • b) = star c * leviC H a b := by
  have h1 : c • b = c.re • b + c.im • (Complex.I • b) := by
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have h2 : Complex.I • (c • b) = c.re • (Complex.I • b) - c.im • b := by
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination ((c.im : ℂ) * b k) * Complex.I_sq
  unfold leviC
  rw [h2, h1]
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring
end ReciprocityTheory.AnForm.A

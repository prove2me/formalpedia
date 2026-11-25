-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:47.988486+00:00
-- url     : https://prove2.me/submissions/38bd5a99-9fdc-49d5-afc8-c2854a7edabb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_sum_leviC_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_isHermitian_of_symm
import Theorems.Thm_ReciprocityTheory_AnForm_hessC_eq_leviC
import Theorems.Thm_ReciprocityTheory_AnForm_sum_mul_leviC


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
theorem _root_.solution (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (h2 : ContDiffAt ℝ 2 φ z)
    (hl : ∀ ξ, 0 ≤ levi φ z ξ) : (hessC φ z).PosSemidef := by
  have hs : IsSymmSndFDerivAt ℝ φ z := h2.isSymmSndFDerivAt (by simp)
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hessC_isHermitian_of_symm φ z hs) fun x => ?_
  have key : star x ⬝ᵥ (hessC φ z *ᵥ x) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star x) (star x) := by
    simp only [dotProduct, mulVec, hessC_eq_leviC, sum_leviC_mul]
    exact sum_mul_leviC _ (star x) (star x)
  rw [key, Complex.nonneg_iff]
  constructor
  · have := hl (star x)
    simpa [leviC, levi] using this
  · simp only [leviC]
    rw [hs (star x) (Complex.I • star x)]
    simp
end ReciprocityTheory.AnForm.A

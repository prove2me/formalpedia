-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.hessC_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:40.990711+00:00
-- url     : https://prove2.me/submissions/769a18d0-b8bb-4cf9-aa6a-68b329e55a96

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_isHermitian__4fd7a1bbb7ba
import Theorems.Thm_ReciprocityTheory_AnForm_M_sum_leviC_right
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
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (h : ∀ w, 0 ≤ levi φ z w) : (hessC φ z).PosSemidef := by
  have hs := hφ.isSymmSndFDerivAt (by simp)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hessC_isHermitian' φ z hφ) fun x => ?_
  have hq : star x ⬝ᵥ ((hessC φ z).mulVec x) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star x) (star x) := by
    rw [Matrix.dotProduct_mulVec]
    simp only [Matrix.vecMul, dotProduct, hessC_eq_leviC, sum_mul_leviC]
    exact sum_leviC_right _ _ _
  rw [hq, Complex.nonneg_iff]
  constructor
  · have := h (star x)
    simp only [levi] at this
    simpa [leviC] using this
  · simp [leviC, hs (star x) (Complex.I • star x)]
end ReciprocityTheory.AnForm.M

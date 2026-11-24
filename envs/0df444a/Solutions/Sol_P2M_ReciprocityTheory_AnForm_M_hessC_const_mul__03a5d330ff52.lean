-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_hessC_const_mul__03a5d330ff52
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:50.048154+00:00
-- url     : https://prove2.me/submissions/d9bbe9d3-ce4f-4c0b-a8de-2ed8441fb510

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian

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
theorem _root_.solution (c : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    hessC (fun w => c * φ w) z = (c : ℂ) • hessC φ z := by
  have h1 : fderiv ℝ (fun w => c * φ w) = c • fderiv ℝ φ := by
    show fderiv ℝ (c • φ) = _
    exact fderiv_const_smul_field c
  have h2 : fderiv ℝ (fderiv ℝ (fun w => c * φ w)) = c • fderiv ℝ (fderiv ℝ φ) := by
    rw [h1]; exact fderiv_const_smul_field c
  ext i j
  simp only [hessC, h2, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  push_cast
  ring
end ReciprocityTheory.AnForm.M

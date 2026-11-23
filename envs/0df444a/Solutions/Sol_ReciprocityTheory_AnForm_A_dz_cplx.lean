-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.dz_cplx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:54.50103+00:00
-- url     : https://prove2.me/submissions/53da6d35-f1c9-4fc1-84f1-d8c8b904fa0c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_cplx

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
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (j : Fin D) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    dz j (cplx v) z = ((fderiv ℝ v z (Pi.single j 1) : ℂ) -
      Complex.I * (fderiv ℝ v z (Complex.I • Pi.single j 1) : ℂ)) / 2 := by
  simp only [dz, fderiv_cplx, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
end ReciprocityTheory.AnForm.A

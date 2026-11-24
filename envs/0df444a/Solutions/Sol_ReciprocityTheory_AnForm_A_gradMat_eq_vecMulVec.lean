-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.gradMat_eq_vecMulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:39.909805+00:00
-- url     : https://prove2.me/submissions/ddf69d2c-a7d4-45e0-8dc6-058a6c627c3a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_dzb_cplx_eq_star

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
theorem _root_.solution (v w : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    gradMat v w z = vecMulVec (fun j => dz j (cplx v) z) (star fun k => dz k (cplx w) z) := by
  ext j k
  simp [gradMat, vecMulVec_apply, dzb_cplx_eq_star]
end ReciprocityTheory.AnForm.A

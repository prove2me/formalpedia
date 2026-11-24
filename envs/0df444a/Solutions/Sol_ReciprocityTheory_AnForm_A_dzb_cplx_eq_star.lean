-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.dzb_cplx_eq_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:31.214514+00:00
-- url     : https://prove2.me/submissions/ef882d4f-0248-4d9e-8f28-fd386c0fdc0b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_cplx
import Theorems.Thm_ReciprocityTheory_AnForm_A_dzb_cplx

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
    dzb j (cplx v) z = star (dz j (cplx v) z) := by
  rw [dz_cplx, dzb_cplx]
  apply Complex.ext <;> simp
end ReciprocityTheory.AnForm.A

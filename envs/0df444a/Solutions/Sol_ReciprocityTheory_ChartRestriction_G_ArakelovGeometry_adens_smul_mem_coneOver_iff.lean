-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_smul_mem_coneOver_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:37:37.897188+00:00
-- url     : https://prove2.me/submissions/3c0a6ad4-69d9-4204-94e4-214f716a18f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_smul_mem_coneOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
variable {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → J → ℂ} {z : J → ℂ}
    {c : ℂ} (hc : c ≠ 0) : c • z ∈ coneOver U γ ↔ z ∈ coneOver U γ := by
  refine ⟨fun h => ?_, fun h => adens_smul_mem_coneOver h hc⟩
  have h2 := adens_smul_mem_coneOver h (inv_ne_zero hc)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

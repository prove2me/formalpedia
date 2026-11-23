-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.rD_comp_qD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:53.009323+00:00
-- url     : https://prove2.me/submissions/24f89d2d-2347-4cb1-92a5-faa5deb4cd77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_qD_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rD_zR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (l : R × R →ₗ[R] R) (i : Fin 2) :
    (rD l).comp (qD i) = TrivSqZeroExt.map ((l (if i = 0 then ((1 : R), (0 : R)) else (0, 1))) • LinearMap.id) := by
  apply DualNumber.algHom_ext
  rw [AlgHom.comp_apply, qD_apply]
  simp only [DualNumber.fst_eps, DualNumber.snd_eps, map_zero, one_smul, zero_add, rD_zR]
  show _ = TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1)
  rw [TrivSqZeroExt.map_inr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, _root_.mul_one]
end ReciprocityTheory.ChartRestriction.G.Chart

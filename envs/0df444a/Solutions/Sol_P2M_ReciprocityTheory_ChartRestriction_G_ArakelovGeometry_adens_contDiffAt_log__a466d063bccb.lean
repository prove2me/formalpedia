-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__a466d063bccb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:46.749187+00:00
-- url     : https://prove2.me/submissions/356c4858-1926-4a54-b52f-30b31af011e7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA

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
theorem _root_.solution {m : ConeMetric ℂ J} (hsm : IsSmoothMetric m) {γ' : (Fin D → ℂ) → J → ℂ}
    {v : Fin D → ℂ} (hγ' : AnalyticAt ℂ γ' v) (hne : γ' v ≠ 0) :
    ContDiffAt ℝ 2 (fun w => Real.log (m.ρ (γ' w))) v := by
  have hρ' : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) m.ρ {z | z ≠ 0} := contDiffOn_infty.1 hsm 2
  have hρ : ContDiffAt ℝ 2 m.ρ (γ' v) := hρ'.contDiffAt (isOpen_ne.mem_nhds hne)
  have hγ : ContDiffAt ℝ 2 γ' v := (hγ'.contDiffAt).restrict_scalars ℝ
  exact (hρ.comp v hγ).log (m.pos _ hne).ne'
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

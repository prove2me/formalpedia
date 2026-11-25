-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_det_resProj_chart_502fde25d34e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:37:09.741634+00:00
-- url     : https://prove2.me/submissions/349c34e8-fa17-446a-b9a0-3cc65d9d624a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_analyticAt_resProj_de06806215a2
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
theorem _root_.solution (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.R.M}
    {j k : Fin R.atlas.n} (hj : x ∈ (R.atlas.chart j).source) (hk : x ∈ (R.atlas.chart k).source)
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart k).symm) (R.atlas.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (R.atlas.chart k ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  set u := R.atlas.chart j x
  have hsu : (R.atlas.chart j).symm u = x := (R.atlas.chart j).left_inv hj
  set T := R.atlas.chart k ∘ (R.atlas.chart j).symm with hTdef
  have huk : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' (R.atlas.chart k).source :=
    ⟨(R.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := R.atlas.holo j k u huk
  have hTu : T u = R.atlas.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_resProj R Ψ x k hk h0
  have heq : resProj R Ψ ∘ (R.atlas.chart j).symm =ᶠ[𝓝 u] (resProj R Ψ ∘ (R.atlas.chart k).symm) ∘ T := by
    filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.atlas.chart k).open_source).mem_nhds
      huk] with v hv
    simp only [hTdef, Function.comp_apply, (R.atlas.chart k).left_inv hv.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt, hTu]
  exact LinearMap.det_comp _ _
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge

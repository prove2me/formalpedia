-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.det_brQ_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:05.546995+00:00
-- url     : https://prove2.me/submissions/8f26213e-2349-47f0-9354-30c6418308b0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_brQ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.X}
    {j k : Fin R.A.n} (hj : x ∈ (R.A.chart j).source) (hk : x ∈ (R.A.chart k).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  have hxj : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmem : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source :=
    ⟨(R.A.chart j).map_source hj, show (R.A.chart j).symm (R.A.chart j x) ∈ (R.A.chart k).source by
      rw [hxj]; exact hk⟩
  have hT : AnalyticAt ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) := R.A.holo j k _ hmem
  have hQk : AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :=
    analyticAt_brQ R Ψ x k hk h0

  have hev : (brQ R Ψ ∘ (R.A.chart j).symm) =ᶠ[𝓝 (R.A.chart j x)]
      (brQ R Ψ ∘ (R.A.chart k).symm) ∘ (R.A.chart k ∘ (R.A.chart j).symm) := by
    have hn : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source ∈
        𝓝 (R.A.chart j x) :=
      ((R.A.chart j).isOpen_inter_preimage_symm (R.A.chart k).open_source).mem_nhds hmem
    filter_upwards [hn] with v hv
    simp only [Function.comp_apply]
    rw [(R.A.chart k).left_inv hv.2]
  have hfx : (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) = R.A.chart k x := by
    simp only [Function.comp_apply]
    rw [hxj]
  have hg : DifferentiableAt ℂ (brQ R Ψ ∘ (R.A.chart k).symm)
      ((R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x)) := by
    rw [hfx]
    exact hQk.differentiableAt
  rw [hev.fderiv_eq, fderiv_comp _ hg hT.differentiableAt, hfx]
  exact LinearMap.det_comp _ _
end ReciprocityTheory.ChartRestriction.G.Geo

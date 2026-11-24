-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.analyticAt_brQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:37.174795+00:00
-- url     : https://prove2.me/submissions/d93c79ee-e5d1-4bfb-be55-874573549a33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_brQ_eq_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_segre_lift

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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  have hxs : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmemT : R.A.chart j x ∈ (R.A.chart j).target := (R.A.chart j).map_source hj
  have hnhd : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x ∈ 𝓝 (R.A.chart j x) := by
    apply Filter.inter_mem ((R.A.chart j).open_target.mem_nhds hmemT)
    apply ((R.A.chart j).continuousAt_symm hmemT).preimage_mem_nhds
    rw [hxs]
    exact (R.isOpen_U x).mem_nhds (R.mem_U x)
  have heq : (fun v => fun i : Fin e => Ψ (segre (R.lift x ((R.A.chart j).symm v))) i.succ /
      Ψ (segre (R.lift x ((R.A.chart j).symm v))) 0) =ᶠ[𝓝 (R.A.chart j x)]
      brQ R Ψ ∘ (R.A.chart j).symm := by
    filter_upwards [hnhd] with v hv
    exact (brQ_eq_local R Ψ hv.2).symm
  refine AnalyticAt.congr ?_ heq
  have hs := analyticAt_segre_lift R Ψ x j ⟨hmemT, by simp [hxs, R.mem_U x]⟩
  have hcomp := analyticAt_pi_iff.mp hs
  rw [analyticAt_pi_iff]
  intro i
  apply AnalyticAt.div (hcomp i.succ) (hcomp 0)
  simpa [hxs] using h0
end ReciprocityTheory.ChartRestriction.G.Geo

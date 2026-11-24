-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_analyticAt_chart_4620b31d9b76
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:13.539375+00:00
-- url     : https://prove2.me/submissions/008b0366-8cbb-4a12-b0bf-b845e2097222

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_projCoord_eq_954a26e906c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_analyticAt_4674083765d3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegular
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
namespace GroundTheory.Heights₂.Heights.Targets.ProjRegular
theorem _root_.solution {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) (h0 : Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0) (j : Fin BV.n)
    (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm) (BV.chart j x) := by
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  have hc : ∀ i : Fin (n + 1), AnalyticAt ℂ
      (fun u => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) i) (BV.chart j x) :=
    fun i => analyticAt_pi_iff.1 (proj_analyticAt Ψ hB x hx) i
  have hG : AnalyticAt ℂ (fun u (i : Fin n) => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) i.succ /
      Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) 0) (BV.chart j x) := by
    rw [analyticAt_pi_iff]
    intro i
    exact (hc i.succ).div (hc 0) (by simpa [hsx] using h0)
  refine hG.congr ?_
  filter_upwards [(lift_analyticAt hB x hx).2] with u hu
  exact (projCoord_eq Ψ hu).symm
end GroundTheory.Heights₂.Heights.Targets.ProjRegular

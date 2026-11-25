-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_analyticAt_resProj_de06806215a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:24:54.907363+00:00
-- url     : https://prove2.me/submissions/b62241bb-c0f5-4a13-bfb9-5acf9e97a47d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resProj_eq_local_78e4d1ce2a23
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_analyticAt_segre_liftAt_a151024a6a4d

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
theorem _root_.solution (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M)
    (j : Fin R.atlas.n) (hj : x ∈ (R.atlas.chart j).source) (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) :
    AnalyticAt ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) := by
  set u := R.atlas.chart j x
  have hsu : (R.atlas.chart j).symm u = x := (R.atlas.chart j).left_inv hj
  have hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x) :=
    ⟨(R.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_src_idx x⟩
  have hH := analyticAt_segre_liftAt R Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (R.liftAt x ((R.atlas.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) i.succ /
        Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis (R.idx x))).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (resProj_eq_local R Ψ hv.2).symm
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_analyticAt_pullQ_ee2a81a860b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:29.195653+00:00
-- url     : https://prove2.me/submissions/2d3455bd-576d-4d3c-bf26-3bba410a490e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_HasStrictFDerivAtEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_pullQ_eq_local_fc4719124d2a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_analyticAt_segre_pull_ac118df51db8

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set
open GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
namespace GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
theorem _root_.solution (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Φ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hH := analyticAt_segre_pull R (v := v) Φ x j hu
  have hH0 : AnalyticAt ℂ (fun w => Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Φ (segre (fun p => R.lift x ((R.A.chart j).symm u) (v p))) 0 ≠ 0 := by
    rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun w => fun i : Fin n =>
      Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) i.succ /
        Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu] with w hw
  exact (pullQ_eq_local R hv Φ hw.2).symm
end GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proof_85eb971859f8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:44.865446+00:00
-- url     : https://prove2.me/submissions/f3bba9c2-d412-4e50-bbfe-ab95ffd85253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_ne_zero_iff_fa3cd001a763
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_analyticAt_4674083765d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_analyticAt_chart_4620b31d9b76
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_det_ne_zero_of_chart_e4ac0590589f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_goodT


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
theorem _root_.solution : ProjRegular.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB
  refine ⟨?_, fun x h0 j hx => analyticAt_chart Ψ hB x h0 j hx, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro x ⟨h0, hdet⟩
    have hj : x ∈ (BV.chart (chartIdx BV x)).source := Classical.choose_spec (BV.cover x)
    have hsx : (BV.chart (chartIdx BV x)).symm (BV.chart (chartIdx BV x) x) = x :=
      (BV.chart _).left_inv hj
    have hg : BV.chart (chartIdx BV x) x ∈ goodT BV (projCoord R Ψ ∘ Subtype.val) (chartIdx BV x) :=
      ⟨(BV.chart _).map_source hj, analyticAt_chart Ψ hB x h0 _ hj, hdet _ hj⟩
    have hD : ∀ᶠ u in 𝓝 (BV.chart (chartIdx BV x) x),
        Ψ (segre (R.lift x.1 ((BV.chart (chartIdx BV x)).symm u).1)) 0 ≠ 0 :=
      (analyticAt_pi_iff.1 (proj_analyticAt Ψ hB x hj) 0).continuousAt.eventually_ne
        (by simpa [hsx] using h0)
    refine ((BV.chart _).eventually_nhds' (· ∈ projRegular R Ψ BV) hj).1 ?_
    filter_upwards [(isOpen_goodT BV _ _).mem_nhds hg, hD, (lift_analyticAt hB x hj).2]
      with u hu hDu hUu
    have h0u := (proj_ne_zero_iff Ψ hUu).2 hDu
    refine ⟨h0u, fun k hk => det_ne_zero_of_chart Ψ hB _ h0u hk ((BV.chart _).map_target hu.1) ?_⟩
    rw [(BV.chart _).right_inv hu.1]
    exact hu.2.2
  · intro x h0 hd
    exact ⟨h0, fun k hk => det_ne_zero_of_chart Ψ hB x h0 hk
      (Classical.choose_spec (BV.cover x)) hd⟩
end GroundTheory.Heights₂.Heights.Targets.ProjRegular

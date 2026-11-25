-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_exists_analytic_log_14266ed031aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:25.844644+00:00
-- url     : https://prove2.me/submissions/35f2b1ab-82ab-4ce1-b6c3-43d0ac0e9901

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_analyticAt_of_exp_eq_f1c35840ad06

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E}
    (hU : IsOpen U) (hc : Convex ℝ U) (hne : U.Nonempty) {h : E → ℂ} (hh : AnalyticOnNhd ℂ h U)
    (h0 : ∀ z ∈ U, h z ≠ 0) :
    ∃ G : E → ℂ, AnalyticOnNhd ℂ G U ∧ ∀ z ∈ U, Complex.exp (G z) = h z := by
  have : ContractibleSpace U := hc.contractibleSpace hne
  have : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  obtain ⟨z₀, hz₀⟩ := hne
  let f : C(U, ℂ) := ⟨U.domRestrict h, hh.continuousOn.domRestrict⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (a₀ := ⟨z₀, hz₀⟩) (e₀ := Complex.log (h z₀))
    (by simp [f, Complex.exp_log (h0 z₀ hz₀)]) (fun x => h0 x x.2)
  classical
  let G : E → ℂ := fun z => if hz : z ∈ U then F ⟨z, hz⟩ else 0
  have hGe : ∀ z ∈ U, Complex.exp (G z) = h z := fun z hz => by
    simpa [G, hz, f] using congrFun hF ⟨z, hz⟩
  have hGc : ContinuousOn G U := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert F.continuous using 1
    funext x
    simp [G, x.2]
  refine ⟨G, fun z hz => analyticAt_of_exp_eq (hGc.continuousAt (hU.mem_nhds hz)) (hh z hz) ?_, hGe⟩
  filter_upwards [hU.mem_nhds hz] with y hy using hGe y hy
end GroundTheory.Heights₂.Heights.Regular

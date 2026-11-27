-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_tendsto_one_799890543335
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:33.269735+00:00
-- url     : https://prove2.me/submissions/7824ea3e-5101-4c32-8c16-b8b67a80b93a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.SliceCut
variable {n : ℕ} (h : HermNorm n)
namespace GroundTheory.Heights₂.Heights.SliceCut
theorem _root_.solution (x : Fin n → ℂ) : Tendsto (fun k => sliceCut h k x) atTop (𝓝 1) := by
  have hdiv : Tendsto (fun k : ℕ => Real.log (h.dualNorm x) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h2 := (tendsto_const_nhds (x := (2 : ℝ))).sub hdiv
  rw [sub_zero] at h2
  have := (Real.smoothTransition.continuous.tendsto 2).comp h2
  rwa [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)] at this
end GroundTheory.Heights₂.Heights.SliceCut

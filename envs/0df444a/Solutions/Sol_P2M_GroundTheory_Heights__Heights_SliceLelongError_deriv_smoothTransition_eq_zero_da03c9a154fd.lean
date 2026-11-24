-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceLelongError_deriv_smoothTransition_eq_zero_da03c9a154fd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:13.516402+00:00
-- url     : https://prove2.me/submissions/c2b06dc8-2c19-42be-9858-ff3340dc22f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceWeightBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLelongError

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
noncomputable section
open GroundTheory.Heights₂.Heights.SliceLelongError
namespace GroundTheory.Heights₂.Heights.SliceLelongError
theorem _root_.solution {s : ℝ} (hs : s < 0 ∨ 1 < s) :
    deriv Real.smoothTransition s = 0 ∧ deriv (deriv Real.smoothTransition) s = 0 := by
  have hloc : deriv Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    rcases hs with hs | hs
    · filter_upwards [Iio_mem_nhds hs] with r hr
      have hc : Real.smoothTransition =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (show r < 0 from hr)] with q hq
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hq)
      rw [hc.deriv_eq, deriv_const]
    · filter_upwards [Ioi_mem_nhds hs] with r hr
      have hc : Real.smoothTransition =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (show 1 < r from hr)] with q hq
        exact Real.smoothTransition.one_of_one_le (le_of_lt hq)
      rw [hc.deriv_eq, deriv_const]
  exact ⟨hloc.eq_of_nhds, by rw [hloc.deriv_eq, deriv_const]⟩
end GroundTheory.Heights₂.Heights.SliceLelongError

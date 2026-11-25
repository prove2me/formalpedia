-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___le_majorant_072e9cf9daee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:26:15.653361+00:00
-- url     : https://prove2.me/submissions/2ceb79a6-93ed-4db3-a725-b1719b65cf33

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_half_pow_5a11f0ddcc99

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (k j : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (ρ a (radii ε) j) t‖ ≤ majorant hε hg k j := by
  have hC := (exists_bound_iteratedDeriv_ρ hε hg k j).choose_spec
  unfold majorant
  split_ifs with hjk
  · linarith [hC.2 t, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j]
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    have := norm_iteratedDeriv_ρ_succ_le_half_pow hε hg n k (by omega) t
    linarith
end GroundTheory.Automorphic.LineKernel

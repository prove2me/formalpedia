-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_metricDefect_standard_888ef6a52a7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:05.965053+00:00
-- url     : https://prove2.me/submissions/c1417b4a-bbdc-430c-b4e4-55a6995c864c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [Fintype ι] (z : Cone n ℂ) (hz : BlockNonzero z) :
    metricDefect (HermLine.standard n) z = 0 := by
  unfold metricDefect
  change Real.log (∏ k, l2Norm (z k)) - ∑ k, ((1 : ℤ) : ℝ) * Real.log (l2Norm (z k)) = 0
  rw [Real.log_prod (fun k _ ↦ (vectorL2Norm_pos (hz k)).ne')]
  simp
end GroundTheory.Heights₂.Heights

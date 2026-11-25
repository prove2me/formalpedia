-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.gN_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:04.295796+00:00
-- url     : https://prove2.me/submissions/d8fbe4c0-14b6-4816-977d-dd4ef5c5de1d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex Filter Topology
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (N : ℕ) (z : ℂ) : ‖gN N z‖ ≤ Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z (N + 1)
  have h2 : 0 ≤ ∑ i ∈ Finset.range (N + 1), ‖z‖ ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  unfold gN expN
  linarith
end ReciprocityTheory.ChartRestriction.G.I2.FPw

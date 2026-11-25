-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.Fs1_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:02:08.697704+00:00
-- url     : https://prove2.me/submissions/1e6f5e93-ddf7-4f6a-bff7-9ecdf3fa7ebf

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_PrimZeroOfNonpos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_EulerCharacteristicLength_primitive_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
namespace ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
theorem _root_.solution (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (Fs1 c a m) (Fs2 c a m t) t := by
  unfold Fs1 Fs2
  apply HasDerivAt.fun_sum
  intro k _
  exact (HasDerivAt.comp_sub_const t (a + k) (primitive_hasDerivAt _)).const_mul (c k)
end ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength

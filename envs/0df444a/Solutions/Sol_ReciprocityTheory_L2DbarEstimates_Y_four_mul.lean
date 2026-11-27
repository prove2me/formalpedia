-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.four_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:55.96385+00:00
-- url     : https://prove2.me/submissions/0a51ea1c-370f-4636-b131-b8b7862f3d06

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_four_mul__6fe18a244e26

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ComplexConjugate
noncomputable section
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_38
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_40
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (f : ℕ) : FOURMulStatement f := by
  intro Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb _ _ ν
  exact (four_mul' f Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν).tsum_eq.symm
end ReciprocityTheory.L2DbarEstimates.Y

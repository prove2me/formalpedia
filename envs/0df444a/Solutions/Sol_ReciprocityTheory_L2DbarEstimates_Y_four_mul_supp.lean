-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.four_mul_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:19.79981+00:00
-- url     : https://prove2.me/submissions/1990dea3-3f2a-4ee7-acf5-40da43032861

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
theorem _root_.solution (f : ℕ) : FOURMulSuppStatement f := by
  intro Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν hne
  by_contra hno
  push Not at hno
  have H := four_mul' f Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν
  have hz : ∀ ν' : Fin f → ℤ, fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν') = 0 := by
    intro ν'
    by_cases h0 : fourCoeff h1 b ν' = 0
    · rw [h0, zero_mul]
    · rw [hno ν' (ν - ν') (by abel) h0, mul_zero]
  have H0 : HasSum (fun ν' : Fin f → ℤ => fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν')) 0 := by
    simp [hz]
  exact hne (H.unique H0)
end ReciprocityTheory.L2DbarEstimates.Y

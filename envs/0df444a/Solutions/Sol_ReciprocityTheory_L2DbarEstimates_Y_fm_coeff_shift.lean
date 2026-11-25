-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fm_coeff_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:29.312895+00:00
-- url     : https://prove2.me/submissions/89476b7b-f09f-4fbe-865d-84c294133ef0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul

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
theorem _root_.solution {f : ℕ} (F : C(UnitAddTorus (Fin f), ℂ)) (ν i : Fin f → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(UnitAddTorus.mFourier (-ν) * F)) i =
      UnitAddTorus.mFourierCoeff (⇑F) (i + ν) := by
  simp only [UnitAddTorus.mFourierCoeff, ContinuousMap.mul_apply, smul_eq_mul]
  congr 1
  funext t
  rw [neg_add, UnitAddTorus.mFourier_add]
  ring
end ReciprocityTheory.L2DbarEstimates.Y

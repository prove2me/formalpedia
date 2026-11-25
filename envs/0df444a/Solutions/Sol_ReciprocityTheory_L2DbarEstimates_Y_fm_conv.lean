-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fm_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:45.979802+00:00
-- url     : https://prove2.me/submissions/91e690ed-ef60-4b4d-92bb-e7334c591691

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fm_coeff_star
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fm_coeff_shift

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
theorem _root_.solution {f : ℕ} (F1 F2 : C(UnitAddTorus (Fin f), ℂ)) (ν : Fin f → ℤ) :
    HasSum (fun ν' => UnitAddTorus.mFourierCoeff (⇑F1) ν' * UnitAddTorus.mFourierCoeff (⇑F2) (ν - ν'))
      (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν) := by
  have H := UnitAddTorus.hasSum_prod_mFourierCoeff ((star F1).toLp 2 volume ℂ)
    ((UnitAddTorus.mFourier (-ν) * F2).toLp 2 volume ℂ)
  have H2 : HasSum (fun i => UnitAddTorus.mFourierCoeff (⇑F1) (-i) *
      UnitAddTorus.mFourierCoeff (⇑F2) (i + ν)) (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν) := by
    convert H using 1
    · funext i
      rw [UnitAddTorus.mFourierCoeff_toLp, UnitAddTorus.mFourierCoeff_toLp, fm_coeff_star,
        fm_coeff_shift]
    · rw [UnitAddTorus.mFourierCoeff]
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (star F1),
        ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
          (UnitAddTorus.mFourier (-ν) * F2)] with t h1 h2
      rw [h1, h2]
      simp
      ring
  rw [← (Equiv.neg (Fin f → ℤ)).hasSum_iff]
  convert H2 using 1
  funext i
  simp [sub_neg_eq_add, add_comm]
end ReciprocityTheory.L2DbarEstimates.Y

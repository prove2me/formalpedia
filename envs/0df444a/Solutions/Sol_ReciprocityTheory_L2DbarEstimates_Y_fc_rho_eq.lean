-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:16.008355+00:00
-- url     : https://prove2.me/submissions/ed8843d1-9975-4b6a-af75-77a856cdbec5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_det_jz


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i : ι) (hi : y ∈ (A.chart i).source) :
    Real.exp (A.ph A.kap (A.pick y) y) /
        ‖(fderiv ℂ (A.zLoc w0 s (A.pick y)) (A.chart (A.pick y) y)).det‖ ^ 2 =
      Real.exp (A.ph A.kap i y) / ‖(fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det‖ ^ 2 := by
  have hp := A.mem_pick y
  have hg : 0 < ‖A.g A.kap (A.pick y) i y‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (A.g_ne A.kap (A.pick y) i y hp hi)) 2
  rw [fc_det_jz A hD hy (A.pick y) i hp hi, A.ph_trans A.kap (A.pick y) i y hp hi, Real.exp_sub,
    Real.exp_log hg, norm_mul, mul_pow]
  ring
end ReciprocityTheory.L2DbarEstimates.Y

-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_psi_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:59.106355+00:00
-- url     : https://prove2.me/submissions/a3a3dd32-b774-44d4-8441-76e0b4dfb2ba

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ne_of_tr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ph_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_jz_det_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_jz_det_trans


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
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
variable {mu0 : La} {σ : ι → Y → ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {y : Y} (hy : y ∈ A.Mset w0 s De) {i : ι}
    (hi : y ∈ (A.chart i).source) : bsPsi A w0 s mu0 σ y = bsPsiC A w0 s mu0 σ i y := by
  have hp := A.mem_pick y
  have hσi : σ i y ≠ 0 := bsA_ne_of_tr A hσ.1.2 hy hi hp (hσ.2 y hy)
  have hg : A.g A.kap (A.pick y) i y ≠ 0 := A.g_ne _ _ _ y hp hi
  have hdet : (jz A w0 s i y).det ≠ 0 := jz_det_ne A hD hF y hy i hi
  unfold bsPsi bsPsiC
  rw [bsA_nsq_chart A hσ.1.2 hy hi, jz_det_trans A hD hF y hy (A.pick y) i hp hi,
    bsA_ph_sub A mu0 A.kap hi, A.ph_trans A.kap (A.pick y) i y hp hi]
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, norm_mul, mul_pow,
    Real.log_mul (by positivity) (by positivity), norm_inv, inv_pow, Real.log_inv]
  ring
end ReciprocityTheory.L2DbarEstimates.Y

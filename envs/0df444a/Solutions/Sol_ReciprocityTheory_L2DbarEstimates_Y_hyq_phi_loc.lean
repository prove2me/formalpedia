-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_phi_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:39:49.866797+00:00
-- url     : https://prove2.me/submissions/7ecceeb8-0a63-4991-b4ff-222b72cbee8c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_nsq_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sigma_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_Mset
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
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
variable   (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {la : La} {σ : ι → Y → ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) (ps : Y → ℝ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    hyPhi A w0 s σ la ps =ᶠ[𝓝 x] fun y => (A.ph la i y + ps y) +
      Real.log (‖(jz A w0 s i y).det * (σ i y)⁻¹‖ ^ 2) := by
  filter_upwards [(A.chart i).open_source.mem_nhds hi, (isOpen_Mset A hD).mem_nhds hx]
    with y hyi hyM
  have hp := A.mem_pick y
  have hσne := hyq_sigma_ne A hσ hyM i hyi
  have hJne := jz_det_ne A hD hF y hyM i hyi
  have e1 := hyq_nsq_chart A _ σ i y hyi (hσ.1.2 i _ y hyM hyi hp)
  have e2 := hyq_nsq_chart A A.kap (fun i y => (jz A w0 s i y).det) i y hyi (by
    show (jz A w0 s i y).det = A.g A.kap i (A.pick y) y * (jz A w0 s (A.pick y) y).det
    rw [jz_det_trans A hD hF y hyM i (A.pick y) hyi hp, mul_comm])
  unfold hyPhi
  rw [e1, e2, A.ph_add A.kap la i y hyi, norm_mul, norm_inv, mul_pow, inv_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_exp, Real.log_exp]
  ring
end ReciprocityTheory.L2DbarEstimates.Y

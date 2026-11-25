-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_logsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:29:30.70521+00:00
-- url     : https://prove2.me/submissions/eed2712a-d171-4494-92e8-bef07d7126fb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


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
theorem _root_.solution {f : V n → ℂ} {p : V n} {O : Set (V n)} (hO : IsOpen O) (hp : p ∈ O)
    (hf : DifferentiableOn ℂ f O) (hne : f p ≠ 0) :
    ContDiffAt ℝ ∞ (fun v => Real.log (‖f v‖ ^ 2)) p := by
  have h1 : ContDiffAt ℂ ∞ f p :=
    (contDiffOn_of_differentiableOn n f O hO hf p hp).contDiffAt (hO.mem_nhds hp)
  have h2 : ContDiffAt ℝ ∞ (fun v => ‖f v‖ ^ 2) p := (h1.restrict_scalars ℝ).norm_sq ℂ
  exact h2.log (by positivity)
end ReciprocityTheory.L2DbarEstimates.Y

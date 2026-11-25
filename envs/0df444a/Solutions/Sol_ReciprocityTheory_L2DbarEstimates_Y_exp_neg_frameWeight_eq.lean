-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.exp_neg_frameWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:34:41.703043+00:00
-- url     : https://prove2.me/submissions/fbab821c-2954-4e7a-8e10-822f2e3b2698

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC

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
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {N : ℕ} (w : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (mu0 : La) (σ : ι → Y → ℂ) (y : Y) (hσ : 0 < A.nsq mu0 σ y)
    (hd : (jz A w0 s (A.pick y) y).det ≠ 0)
    (hS : 0 < ∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) :
    Real.exp (-bsPh0 A w w0 s mu0 σ y) =
      A.nsq mu0 σ y * (Real.exp (A.ph A.kap (A.pick y) y) / ‖(jz A w0 s (A.pick y) y).det‖ ^ 2) *
        (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  unfold bsPh0 bsPsi
  have hd2 : 0 < ‖(jz A w0 s (A.pick y) y).det‖ ^ 2 := by positivity
  rw [Real.rpow_def_of_pos hS]
  rw [show -(-Real.log (A.nsq mu0 σ y) - A.ph A.kap (A.pick y) y +
      Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2) +
      1 / 2 * Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2)) =
      Real.log (A.nsq mu0 σ y) + A.ph A.kap (A.pick y) y -
        Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2) +
        Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) * (-(1 / 2 : ℝ)) by ring]
  rw [Real.exp_add, Real.exp_sub, Real.exp_add, Real.exp_log hσ, Real.exp_log hd2]
  ring
end ReciprocityTheory.L2DbarEstimates.Y

-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsC_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:33:36.529678+00:00
-- url     : https://prove2.me/submissions/2195b147-7559-4529-a645-492c4e2cf858

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
theorem _root_.solution (Fn nσ a Z S ρ : ℝ) (m : ℕ) (ha : 0 < a) (hZ : 0 < Z) (hS : 0 < S) :
    Fn * nσ * a ^ m * (a * Z) ^ (-((m : ℝ) - 1 / 2)) * (a * S) ^ (-(1 / 2 : ℝ)) * ρ =
      Fn * Z ^ (-((m : ℝ) - 1 / 2)) * (nσ * ρ * S ^ (-(1 / 2 : ℝ))) := by
  rw [Real.mul_rpow ha.le hZ.le, Real.mul_rpow ha.le hS.le]
  have key : a ^ m * a ^ (-((m : ℝ) - 1 / 2)) * a ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha, ← Real.rpow_add ha]
    ring_nf; exact Real.rpow_zero a
  calc Fn * nσ * a ^ m * (a ^ (-((m : ℝ) - 1 / 2)) * Z ^ (-((m : ℝ) - 1 / 2))) *
        (a ^ (-(1 / 2 : ℝ)) * S ^ (-(1 / 2 : ℝ))) * ρ
      = Fn * Z ^ (-((m : ℝ) - 1 / 2)) * (nσ * ρ * S ^ (-(1 / 2 : ℝ))) *
          (a ^ m * a ^ (-((m : ℝ) - 1 / 2)) * a ^ (-(1 / 2 : ℝ))) := by ring
    _ = _ := by rw [key, mul_one]
end ReciprocityTheory.L2DbarEstimates.Y

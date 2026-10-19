-- Prove2me | solution 1 for QuantumParallelRepetition.totalSamplingLoss_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/58d1e036-79d8-41e0-bd02-1a69d2aff1a8

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open Filter
open scoped Topology
namespace QuantumParallelRepetition
theorem _root_.solution
    {ι : Type*} {l : Filter ι}
    (K₀ : ℝ) {α η lam : ι → ℝ}
    (hα : Tendsto α l (𝓝 0))
    (hη : Tendsto η l (𝓝 0))
    (hlam : Tendsto lam l (𝓝 0)) :
    Tendsto (fun i => totalSamplingLoss K₀ (α i) (η i) (lam i))
      l (𝓝 0) := by
  have hαroot :
      Tendsto (fun i => (α i) ^ (1 / 12 : ℝ)) l (𝓝 0) :=
    hα.rpow_const_nhds_zero (by norm_num)
  have hηscaled : Tendsto (fun i => 32 * η i) l (𝓝 0) := by
    simpa using hη.const_mul (32 : ℝ)
  have hηroot :
      Tendsto (fun i => (32 * η i) ^ (1 / 12 : ℝ)) l (𝓝 0) :=
    hηscaled.rpow_const_nhds_zero (by norm_num)
  have hηeight : Tendsto (fun i => 8 * η i) l (𝓝 0) := by
    simpa using hη.const_mul (8 : ℝ)
  have hsqrt : Tendsto (fun i => Real.sqrt (8 * η i)) l (𝓝 0) := by
    simpa using hηeight.sqrt
  have hquantum :
      Tendsto
        (fun i => K₀ * ((α i) ^ (1 / 12 : ℝ) +
          (32 * η i) ^ (1 / 12 : ℝ))) l (𝓝 0) := by
    simpa using (hαroot.add hηroot).const_mul K₀
  have hceiling :
      Tendsto (fun i => universalErrorCeiling K₀ * lam i)
        l (𝓝 0) := by
    simpa using hlam.const_mul (universalErrorCeiling K₀)
  have hinner :
      Tendsto
        (fun i => K₀ * ((α i) ^ (1 / 12 : ℝ) +
            (32 * η i) ^ (1 / 12 : ℝ)) +
          Real.sqrt (8 * η i) + universalErrorCeiling K₀ * lam i)
        l (𝓝 0) := by
    simpa using (hquantum.add hsqrt).add hceiling
  have hclassical : Tendsto (fun i => 5 * lam i) l (𝓝 0) := by
    simpa using hlam.const_mul (5 : ℝ)
  have hdouble :
      Tendsto
        (fun i => 2 *
          (K₀ * ((α i) ^ (1 / 12 : ℝ) +
              (32 * η i) ^ (1 / 12 : ℝ)) +
            Real.sqrt (8 * η i) + universalErrorCeiling K₀ * lam i))
        l (𝓝 0) := by
    simpa using hinner.const_mul (2 : ℝ)
  simpa [totalSamplingLoss] using hclassical.add hdouble
end QuantumParallelRepetition

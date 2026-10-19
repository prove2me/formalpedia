-- Prove2me | solution 1 for QuantumParallelRepetition.totalSamplingLoss_eventually_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/48791692-3921-4501-a72b-ee408bf07082

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_totalSamplingLoss_tendsto_zero

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
    (hlam : Tendsto lam l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, totalSamplingLoss K₀ (α i) (η i) (lam i) < ε :=
  (totalSamplingLoss_tendsto_zero K₀ hα hη hlam).eventually
    (gt_mem_nhds hε)
end QuantumParallelRepetition

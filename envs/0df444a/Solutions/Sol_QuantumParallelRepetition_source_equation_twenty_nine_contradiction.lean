-- Prove2me | solution 1 for QuantumParallelRepetition.source_equation_twenty_nine_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/2fdd7c61-6f6f-4fa2-a292-51369475a43e

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_winProbabilities_bddAbove

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
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (S : Strategy G)
    (K₀ α η lam : ℝ)
    (hbound :
      roundedWinningLowerBound (1 - entangledValue G)
        K₀ α η lam ≤ S.winProbability)
    (herror :
      totalSamplingLoss K₀ α η lam < (1 - entangledValue G) / 2) :
    False := by
  have hsup : S.winProbability ≤ entangledValue G := by
    unfold entangledValue
    exact le_csSup (winProbabilities_bddAbove G) ⟨S, rfl⟩
  unfold roundedWinningLowerBound at hbound
  linarith
end QuantumParallelRepetition

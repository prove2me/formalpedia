-- Prove2me | solution 1 for QuantumParallelRepetition.exact_totalSamplingLoss_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/74f0e613-0a02-496d-afc9-75deb00a866f

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
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    {K₀ α₁ α₂ η₁ η₂ lam₁ lam₂ : ℝ}
    (constant_nonnegative : 0 ≤ K₀)
    (alpha_nonnegative : 0 ≤ α₁)
    (alpha_le : α₁ ≤ α₂)
    (eta_nonnegative : 0 ≤ η₁)
    (eta_le : η₁ ≤ η₂)
    (lam_le : lam₁ ≤ lam₂) :
    totalSamplingLoss K₀ α₁ η₁ lam₁ ≤
      totalSamplingLoss K₀ α₂ η₂ lam₂ := by
  have ceiling_nonnegative : 0 ≤ universalErrorCeiling K₀ := by
    unfold universalErrorCeiling
    positivity
  have alpha_root :
      α₁ ^ (1 / 12 : ℝ) ≤ α₂ ^ (1 / 12 : ℝ) :=
    Real.rpow_le_rpow alpha_nonnegative alpha_le (by norm_num)
  have eta_root :
      (32 * η₁) ^ (1 / 12 : ℝ) ≤
        (32 * η₂) ^ (1 / 12 : ℝ) := by
    apply Real.rpow_le_rpow
    · positivity
    · linarith
    · norm_num
  have eta_sqrt :
      Real.sqrt (8 * η₁) ≤ Real.sqrt (8 * η₂) := by
    apply Real.sqrt_le_sqrt
    linarith
  unfold totalSamplingLoss
  gcongr
end QuantumParallelRepetition

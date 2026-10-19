-- Prove2me | solution 1 for SpherePacking.finiteHilbertSchmidtKernel_three_channel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/dd1d2b80-6ea5-46d0-b3e6-5fdb76237526

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_orthogonal_three_channel_inner

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
namespace SpherePacking
theorem _root_.solution
    {α ι F E : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (basis : OrthonormalBasis ι ℝ F)
    (P M R : α → F →ₗ[ℝ] E) (a b : ℝ)
    (hPM : ∀ x y i, ⟪P x (basis i), M y (basis i)⟫_ℝ = 0)
    (hPR : ∀ x y i, ⟪P x (basis i), R y (basis i)⟫_ℝ = 0)
    (hMR : ∀ x y i, ⟪M x (basis i), R y (basis i)⟫_ℝ = 0)
    (x y : α) :
    finiteHilbertSchmidtKernel basis
        (fun z => a • P z + b • M z + R z) x y =
      a ^ 2 * finiteHilbertSchmidtKernel basis P x y +
        b ^ 2 * finiteHilbertSchmidtKernel basis M x y +
        finiteHilbertSchmidtKernel basis R x y := by
  unfold finiteHilbertSchmidtKernel
  calc
    (∑ i : ι,
      ⟪(a • P x + b • M x + R x) (basis i),
        (a • P y + b • M y + R y) (basis i)⟫_ℝ) =
        ∑ i : ι,
          (a ^ 2 * ⟪P x (basis i), P y (basis i)⟫_ℝ +
            b ^ 2 * ⟪M x (basis i), M y (basis i)⟫_ℝ +
            ⟪R x (basis i), R y (basis i)⟫_ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [LinearMap.add_apply, LinearMap.smul_apply] using
        orthogonal_three_channel_inner
          (fun z => P z (basis i))
          (fun z => M z (basis i))
          (fun z => R z (basis i)) a b
          (fun u v => hPM u v i)
          (fun u v => hPR u v i)
          (fun u v => hMR u v i) x y
    _ = a ^ 2 * (∑ i : ι, ⟪P x (basis i), P y (basis i)⟫_ℝ) +
        b ^ 2 * (∑ i : ι, ⟪M x (basis i), M y (basis i)⟫_ℝ) +
        (∑ i : ι, ⟪R x (basis i), R y (basis i)⟫_ℝ) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
end SpherePacking

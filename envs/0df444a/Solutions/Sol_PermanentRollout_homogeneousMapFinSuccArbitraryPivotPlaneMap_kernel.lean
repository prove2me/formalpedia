-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccArbitraryPivotPlaneMap_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/ed413584-cedf-49fc-8353-0930a95ae559

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccFirstPivotPlaneMap_kernel

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ} (c : Fin (n + 1) → ℂ)
    (j : Fin (n + 1)) (hj : c j ≠ 0)
    (u : Fin n → ℂ) :
    ∑ i : Fin (n + 1),
      c i * homogeneousMapFinSuccArbitraryPivotPlaneMap c j u i = 0 := by
  let swap := Equiv.swap (0 : Fin (n + 1)) j
  let d : Fin (n + 1) → ℂ := fun i => c (swap.symm i)
  have hd : d 0 ≠ 0 := by
    simpa [d, swap] using hj
  have hsum := homogeneousMapFinSuccFirstPivotPlaneMap_kernel d hd u
  have hreindex :
      (∑ i : Fin (n + 1),
        c i * homogeneousMapFinSuccArbitraryPivotPlaneMap c j u i) =
      ∑ i : Fin (n + 1),
        d i * homogeneousMapFinSuccFirstPivotPlaneMap d u i := by
    refine Fintype.sum_equiv swap
      (fun i : Fin (n + 1) =>
        c i * homogeneousMapFinSuccArbitraryPivotPlaneMap c j u i)
      (fun i : Fin (n + 1) =>
        d i * homogeneousMapFinSuccFirstPivotPlaneMap d u i) ?_
    intro i
    simp [d, swap, homogeneousMapFinSuccArbitraryPivotPlaneMap,
      homogeneousMapFinSuccPivotPermutation]
  rw [hreindex]
  exact hsum
end PermanentRollout

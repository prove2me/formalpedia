-- Prove2me | solution 1 for QuantumParallelRepetition.posSemidef_kernel_of_sub_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/4de27e65-5604-47aa-ae78-e35834802e6f

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hA : A.PosSemidef) (hsub : (F - A).PosSemidef)
    {x : d → ℂ} (hx : F *ᵥ x = 0) :
    A *ᵥ x = 0 := by
  apply (hA.dotProduct_mulVec_zero_iff x).mp
  have hA_nonneg : 0 ≤ star x ⬝ᵥ (A *ᵥ x) :=
    hA.dotProduct_mulVec_nonneg x
  have hsub_nonneg : 0 ≤ star x ⬝ᵥ ((F - A) *ᵥ x) :=
    hsub.dotProduct_mulVec_nonneg x
  have hzero :
      star x ⬝ᵥ (A *ᵥ x) +
        star x ⬝ᵥ ((F - A) *ᵥ x) = 0 := by
    calc
      star x ⬝ᵥ (A *ᵥ x) +
          star x ⬝ᵥ ((F - A) *ᵥ x) =
        star x ⬝ᵥ ((A + (F - A)) *ᵥ x) := by
          rw [Matrix.add_mulVec, dotProduct_add]
      _ = star x ⬝ᵥ (F *ᵥ x) := by
        have hsum : A + (F - A) = F := by abel
        rw [hsum]
      _ = 0 := by rw [hx]; simp
  exact (add_eq_zero_iff_of_nonneg hA_nonneg hsub_nonneg).mp hzero |>.1
end QuantumParallelRepetition

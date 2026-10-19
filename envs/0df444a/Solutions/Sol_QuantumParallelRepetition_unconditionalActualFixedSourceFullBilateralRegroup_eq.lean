-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFixedSourceFullBilateralRegroup_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/80377383-c2e6-460f-93ec-d36b7325a383

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {B N d L m : ℕ} {R : Type} (j : Fin L) :
    unconditionalSourcePhysicalCleanedFullBilateralRegroup
        (R := R) (B := B) (N := N) (d := d) (m := m) j =
      (unconditionalSelectedRetainedBilateralRegroup
        (UnconditionalSelectedCopyLocalIndex B d N m)
        (UnconditionalActualCleanedSelectedRetainedIndex
          (N := N) (d := d) j R)).trans
        (Equiv.prodCongr
          (Equiv.refl
            (UnconditionalSelectedCopyLocalIndex B d N m ×
             UnconditionalSelectedCopyLocalIndex B d N m))
          (unconditionalActualFixedSourceRetainedHistoryPairEquiv
            (N := N) (d := d) (R := R) j)) := by
  apply Equiv.ext
  rintro ⟨⟨selectedA, beforeA, afterA, phaseA⟩,
    ⟨selectedB, beforeB, afterB, phaseB⟩⟩
  rfl
end QuantumParallelRepetition

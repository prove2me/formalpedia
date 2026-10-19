-- Prove2me | solution 1 for PermanentRollout.partitionIncidenceGlobalColumnLift_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/688d81e2-e013-4375-8495-9236eb88889c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (t s d : ℕ) (a : Fin s) (i : Fin t) :
    partitionIncidenceGlobalColumnLift t s d
      (partitionIncidenceEquation t s d a i) =
      incidenceUniversalPartitionDerivative d i
        (partitionIncidenceGlobalUniversalParameter t s d)
        (fun row : Fin t => (a, row)) := by
  classical
  unfold partitionIncidenceGlobalColumnLift partitionIncidenceEquation
    incidenceUniversalPartitionDerivative
  simp only [map_sum, map_mul, map_prod, map_sub,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    RingHom.coe_comp, Function.comp_apply,
    MvPolynomial.algebraMap_eq]
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro partition _
  congr 1
  unfold incidenceUniversalPartitionBlockFactor
  calc
    (∏ block ∈ partition.parts.attach,
      (MvPolynomial.C
        (MvPolynomial.X
          (Sum.inl ⟨block.1,
            partition.nonempty_of_mem_parts block.2⟩)) -
        ∏ row ∈ block.1,
          (MvPolynomial.X (a, row) :
            MvPolynomial (Fin s × Fin t)
              ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ))))) =
      ∏ block ∈ partition.parts.attach,
        (MvPolynomial.C
          (partitionIncidenceGlobalUniversalParameter t s d block.1) -
          ∏ row ∈ block.1,
            (MvPolynomial.X (a, row) :
              MvPolynomial (Fin s × Fin t)
                ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)))) := by
      apply Finset.prod_congr rfl
      intro block _
      simp [partitionIncidenceGlobalUniversalParameter,
        partition.nonempty_of_mem_parts block.2]
    _ = ∏ block ∈ partition.parts,
        (MvPolynomial.C
          (partitionIncidenceGlobalUniversalParameter t s d block) -
          ∏ row ∈ block,
            (MvPolynomial.X (a, row) :
              MvPolynomial (Fin s × Fin t)
                ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)))) :=
      Finset.prod_attach partition.parts
        (fun block =>
          (MvPolynomial.C
            (partitionIncidenceGlobalUniversalParameter t s d block) -
            ∏ row ∈ block,
              (MvPolynomial.X (a, row) :
                MvPolynomial (Fin s × Fin t)
                  ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)))))
end PermanentRollout

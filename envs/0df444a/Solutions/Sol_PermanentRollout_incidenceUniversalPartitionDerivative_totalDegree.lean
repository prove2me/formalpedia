-- Prove2me | solution 1 for PermanentRollout.incidenceUniversalPartitionDerivative_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/f00c4716-90b2-458f-8d39-a45ed31209bd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_incidenceUniversalPartitionBlockFactor_totalDegree

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {t : ℕ} {ι B : Type*} [CommRing B] [Nontrivial B] [Algebra ℂ B]
    (d : ℕ) (i : Fin t)
    (parameter : Finset (Fin t) → B) (index : Fin t → ι) :
    (incidenceUniversalPartitionDerivative d i parameter index).totalDegree ≤
      d - 1 := by
  classical
  unfold incidenceUniversalPartitionDerivative
  apply MvPolynomial.totalDegree_finsetSum_le
  intro rows hrows
  have hrowscard : rows.card = d - 1 :=
    (Finset.mem_powersetCard.mp hrows).2
  apply MvPolynomial.totalDegree_finsetSum_le
  intro partition _
  calc
    (MvPolynomial.C (algebraMap ℂ B (partitionMobius partition)) *
      incidenceUniversalPartitionBlockFactor parameter index partition).totalDegree ≤
        (MvPolynomial.C (algebraMap ℂ B (partitionMobius partition)) :
          MvPolynomial ι B).totalDegree +
            (incidenceUniversalPartitionBlockFactor parameter index partition).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (incidenceUniversalPartitionBlockFactor parameter index partition).totalDegree := by
      rw [MvPolynomial.totalDegree_C, Nat.zero_add]
    _ ≤ rows.card :=
      incidenceUniversalPartitionBlockFactor_totalDegree parameter index partition
    _ = d - 1 := hrowscard
end PermanentRollout

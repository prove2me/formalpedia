-- Prove2me | solution 1 for PermanentRollout.incidenceUniversalPartitionBlockFactor_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/2eaf91b8-ee1f-4ae1-9205-20e4fb87b553

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {t : ℕ} {ι B : Type*} [CommRing B] [Nontrivial B]
    (parameter : Finset (Fin t) → B) (index : Fin t → ι)
    {rows : Finset (Fin t)} (partition : Finpartition rows) :
    (incidenceUniversalPartitionBlockFactor parameter index partition).totalDegree ≤
      rows.card := by
  classical
  unfold incidenceUniversalPartitionBlockFactor
  calc
    (∏ block ∈ partition.parts,
        (MvPolynomial.C (parameter block) -
          ∏ row ∈ block, (MvPolynomial.X (index row) :
            MvPolynomial ι B))).totalDegree ≤
      ∑ block ∈ partition.parts,
        (MvPolynomial.C (parameter block) -
          ∏ row ∈ block, (MvPolynomial.X (index row) :
            MvPolynomial ι B)).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ block ∈ partition.parts, block.card := by
      apply Finset.sum_le_sum
      intro block _
      calc
        (MvPolynomial.C (parameter block) -
          ∏ row ∈ block, (MvPolynomial.X (index row) :
            MvPolynomial ι B)).totalDegree ≤
          max (MvPolynomial.C (parameter block) : MvPolynomial ι B).totalDegree
            (∏ row ∈ block,
              (MvPolynomial.X (index row) : MvPolynomial ι B)).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
        _ ≤ block.card := by
          rw [MvPolynomial.totalDegree_C, Nat.max_eq_right (Nat.zero_le _)]
          calc
            (∏ row ∈ block,
              (MvPolynomial.X (index row) : MvPolynomial ι B)).totalDegree ≤
              ∑ row ∈ block,
                (MvPolynomial.X (index row) : MvPolynomial ι B).totalDegree :=
              MvPolynomial.totalDegree_finsetProd _ _
            _ ≤ block.card := by simp
    _ = rows.card := partition.sum_card_parts
end PermanentRollout

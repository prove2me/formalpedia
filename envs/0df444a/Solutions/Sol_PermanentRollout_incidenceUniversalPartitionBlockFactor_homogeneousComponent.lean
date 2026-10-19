-- Prove2me | solution 1 for PermanentRollout.incidenceUniversalPartitionBlockFactor_homogeneousComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/b500a147-6e6a-4c5a-9313-593c17e1d3e3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partition_selected_blocks_card_lt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {t : ℕ} {ι B : Type*} [CommRing B]
    (parameter : Finset (Fin t) → B) (index : Fin t → ι)
    {rows : Finset (Fin t)} (partition : Finpartition rows) :
    MvPolynomial.homogeneousComponent rows.card
      (incidenceUniversalPartitionBlockFactor parameter index partition) =
      MvPolynomial.C ((-1 : B) ^ partition.parts.card) *
        ∏ row ∈ rows, MvPolynomial.X (index row) := by
  classical
  have hblock (block : Finset (Fin t)) :
      (∏ row ∈ block,
        (MvPolynomial.X (index row) : MvPolynomial ι B)).IsHomogeneous
          block.card := by
    convert MvPolynomial.IsHomogeneous.prod block
      (fun row => (MvPolynomial.X (index row) : MvPolynomial ι B))
      (fun _ => 1)
      (fun row _ => MvPolynomial.isHomogeneous_X B (index row)) using 1
    simp
  have hterm (selected : Finset (Finset (Fin t))) :
      (((-1 : MvPolynomial ι B) ^ selected.card *
          (∏ block ∈ partition.parts \ selected,
            MvPolynomial.C (parameter block))) *
          ∏ block ∈ selected,
            ∏ row ∈ block, MvPolynomial.X (index row)).IsHomogeneous
          (∑ block ∈ selected, block.card) := by
    have hsign :
        ((-1 : MvPolynomial ι B) ^ selected.card).IsHomogeneous 0 := by
      convert (MvPolynomial.isHomogeneous_C ι (-1 : B)).pow selected.card
        using 1 <;> simp
    have hconstants :
        (∏ block ∈ partition.parts \ selected,
          (MvPolynomial.C (parameter block) : MvPolynomial ι B)).IsHomogeneous 0 := by
      convert MvPolynomial.IsHomogeneous.prod
        (partition.parts \ selected)
        (fun block => (MvPolynomial.C (parameter block) : MvPolynomial ι B))
        (fun _ => 0)
        (fun block _ => MvPolynomial.isHomogeneous_C ι (parameter block))
        using 1
      simp
    have hmonomials :
        (∏ block ∈ selected,
          ∏ row ∈ block,
            (MvPolynomial.X (index row) : MvPolynomial ι B)).IsHomogeneous
          (∑ block ∈ selected, block.card) :=
      MvPolynomial.IsHomogeneous.prod selected
        (fun block => ∏ row ∈ block,
          (MvPolynomial.X (index row) : MvPolynomial ι B))
        (fun block => block.card)
        (fun block _ => hblock block)
    simpa using (hsign.mul hconstants).mul hmonomials
  unfold incidenceUniversalPartitionBlockFactor
  rw [Finset.prod_sub, map_sum]
  refine (Finset.sum_eq_single_of_mem partition.parts
    (Finset.mem_powerset_self partition.parts) ?_).trans ?_
  · intro selected hselected hne
    have hlt := partition_selected_blocks_card_lt partition selected
      (Finset.mem_powerset.mp hselected) hne
    rw [MvPolynomial.homogeneousComponent_of_mem (hterm selected),
      if_neg (by omega)]
  · have hfull :
        (((-1 : MvPolynomial ι B) ^ partition.parts.card *
            (∏ block ∈ partition.parts \ partition.parts,
              MvPolynomial.C (parameter block))) *
            ∏ block ∈ partition.parts,
              ∏ row ∈ block, MvPolynomial.X (index row)).IsHomogeneous
          rows.card := by
      simpa only [partition.sum_card_parts] using hterm partition.parts
    rw [MvPolynomial.homogeneousComponent_eq_self hfull]
    simp only [Finset.sdiff_self, Finset.prod_empty, mul_one]
    have hprod :
        (∏ block ∈ partition.parts,
          ∏ row ∈ block,
            (MvPolynomial.X (index row) : MvPolynomial ι B)) =
          ∏ row ∈ rows, MvPolynomial.X (index row) := by
      calc
        (∏ block ∈ partition.parts,
          ∏ row ∈ block,
            (MvPolynomial.X (index row) : MvPolynomial ι B)) =
            ∏ row ∈ partition.parts.biUnion id,
              MvPolynomial.X (index row) :=
          (Finset.prod_biUnion partition.disjoint).symm
        _ = ∏ row ∈ rows, MvPolynomial.X (index row) := by
          simp only [partition.biUnion_parts]
    rw [hprod]
    simp
end PermanentRollout

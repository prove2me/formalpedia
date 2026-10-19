-- Prove2me | solution 1 for PermanentRollout.incidenceUniversalPartitionDerivative_homogeneousComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/386c7539-e386-4345-a1ad-8a2c1622f674

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partitionMobius_mul_neg_one_pow
import Theorems.Thm_PermanentRollout_partition_cycle_factorial_complex
import Theorems.Thm_PermanentRollout_incidenceUniversalPartitionBlockFactor_homogeneousComponent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {t : ℕ} {ι B : Type*} [CommRing B] [Algebra ℂ B]
    (d : ℕ) (i : Fin t)
    (parameter : Finset (Fin t) → B) (index : Fin t → ι) :
    MvPolynomial.homogeneousComponent (d - 1)
      (incidenceUniversalPartitionDerivative d i parameter index) =
      MvPolynomial.C
          (algebraMap ℂ B
            (((-1 : ℂ) ^ (d - 1)) * ((d - 1).factorial : ℂ))) *
        MvPolynomial.map (algebraMap ℂ B)
          (MvPolynomial.rename index
            (deletedCoordinateEsymmPolynomial t (d - 1) i)) := by
  classical
  unfold incidenceUniversalPartitionDerivative
  rw [map_sum]
  have hrename :
      MvPolynomial.map (algebraMap ℂ B)
        (MvPolynomial.rename index
          (deletedCoordinateEsymmPolynomial t (d - 1) i)) =
      ∑ rows ∈ ((Finset.univ : Finset (Fin t)).erase i).powersetCard (d - 1),
        ∏ row ∈ rows, (MvPolynomial.X (index row) : MvPolynomial ι B) := by
    rw [deletedCoordinateEsymmPolynomial, Finset.esymm_map_val]
    simp only [map_sum, map_prod, MvPolynomial.rename_X,
      MvPolynomial.map_X]
  rw [hrename, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rows hrows
  have hcard : rows.card = d - 1 :=
    (Finset.mem_powersetCard.mp hrows).2
  rw [map_sum]
  calc
    (∑ partition : Finpartition rows,
        MvPolynomial.homogeneousComponent (d - 1)
          (MvPolynomial.C (algebraMap ℂ B (partitionMobius partition)) *
            incidenceUniversalPartitionBlockFactor parameter index partition)) =
      ∑ partition : Finpartition rows,
        MvPolynomial.C
          (algebraMap ℂ B
            (((-1 : ℂ) ^ (d - 1)) *
              ∏ block ∈ partition.parts,
                ((block.card - 1).factorial : ℂ))) *
          ∏ row ∈ rows, MvPolynomial.X (index row) := by
      apply Finset.sum_congr rfl
      intro partition _
      rw [MvPolynomial.homogeneousComponent_C_mul, ← hcard,
        incidenceUniversalPartitionBlockFactor_homogeneousComponent]
      have hmobi := congrArg (algebraMap ℂ B)
        (partitionMobius_mul_neg_one_pow partition)
      simp only [map_mul, map_pow, map_neg, map_one] at hmobi
      rw [← mul_assoc, ← MvPolynomial.C_mul, hmobi, hcard]
      simp only [map_mul, map_pow, map_neg, map_one]
    _ = MvPolynomial.C
          (algebraMap ℂ B
            (((-1 : ℂ) ^ (d - 1)) * ((d - 1).factorial : ℂ))) *
          ∏ row ∈ rows, MvPolynomial.X (index row) := by
      rw [← Finset.sum_mul, ← map_sum]
      congr 2
      rw [← map_sum, ← Finset.mul_sum,
        partition_cycle_factorial_complex rows, hcard]
end PermanentRollout

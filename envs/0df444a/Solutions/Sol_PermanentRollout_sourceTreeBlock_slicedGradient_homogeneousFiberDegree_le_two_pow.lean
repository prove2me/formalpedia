-- Prove2me | solution 1 for PermanentRollout.sourceTreeBlock_slicedGradient_homogeneousFiberDegree_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/a29573b9-1bee-4140-b758-1d0c7c11caf5

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_normalizedPermanent_slicedGradient_homogeneousFiberDegree_le_two_pow
import Theorems.Thm_PermanentRollout_sourceTreeBlock_affine_permanent_specialization
import Theorems.Thm_PermanentRollout_floor_sourceTreeSeparatedMinorSum_eq_sourceSeparatedBlockMinorSum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    (circuit : ArithmeticCircuit (Fin n × Fin n))
    (hpermanent : circuit.polynomial = permanent n)
    (tree : BlockTree (Fin (blockCount n d)))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ)
    (W : (Fin (sliceRank n d) → ℂ) →ₗ[ℂ]
      (Fin (blockVariables n d) → ℂ))
    (A : (Fin (blockVariables n d) → ℂ) →ₗ[ℂ]
      (Fin (sliceRank n d) → ℂ))
    (hhomogeneous : ∀ i : Fin (sliceRank n d),
      (slicedGradientPolynomial
        (sourceSeparatedBlockMinorSum n d
          (sourceTreeBlockWeight (blockCount n d) d tree)) W A i).IsHomogeneous
        (d - 1))
    (hzero : ∀ point : Fin (sliceRank n d) → ℂ,
      (∀ i, MvPolynomial.eval point
        (slicedGradientPolynomial
          (sourceSeparatedBlockMinorSum n d
            (sourceTreeBlockWeight (blockCount n d) d tree)) W A i) = 0) ↔
        point = 0) :
    (d - 1) ^ sliceRank n d ≤ 2 ^ (3 * circuit.size) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))
  have hζ : IsPrimitiveRoot ζ d :=
    Complex.isPrimitiveRoot_exp d (by omega)
  obtain ⟨substitution, coefficient, hcoefficient, hspecialization⟩ :=
    sourceTreeBlock_affine_permanent_specialization
      hd hn hζ tree hnodup hleaves
  have hsource :
      MvPolynomial.aeval
          (fun ij => (substitution ij).polynomial) (permanent n) =
        MvPolynomial.C coefficient *
          sourceSeparatedBlockMinorSum n d
            (sourceTreeBlockWeight (blockCount n d) d tree) := by
    rw [floor_sourceTreeSeparatedMinorSum_eq_sourceSeparatedBlockMinorSum]
      at hspecialization
    exact hspecialization
  exact normalizedPermanent_slicedGradient_homogeneousFiberDegree_le_two_pow
    circuit hpermanent substitution
    (sourceSeparatedBlockMinorSum n d
      (sourceTreeBlockWeight (blockCount n d) d tree))
    coefficient hcoefficient hsource W A (d - 1) (by omega)
    hhomogeneous hzero
end PermanentRollout

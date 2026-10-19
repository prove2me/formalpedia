-- Prove2me | solution 1 for PermanentRollout.sourceTreeBlock_affine_permanent_specialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/aaff57d5-3f5a-4824-8957-c5b91b254e0e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceTreeBlockMatrix_permanent_eq_separated_minorSum
import Theorems.Thm_PermanentRollout_sourceBlock_affine_permanent_specialization
import Theorems.Thm_PermanentRollout_sourceTreeBlockCommonFactor_ne_zero
import Theorems.Thm_PermanentRollout_sourceBlockMatrix_rectangularPermanent_flatten

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
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree (Fin (blockCount n d)))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    ∃ (sub : Fin n × Fin n → FreeAffineInput (Fin (blockVariables n d)))
      (c : ℂ), c ≠ 0 ∧
        MvPolynomial.aeval (fun ij => (sub ij).polynomial)
            (permanent n) =
          MvPolynomial.C c *
            MvPolynomial.rename
              (finProdFinEquiv :
                Fin (blockRows n d) × Fin (blockColumns n d) ≃
                  Fin (blockVariables n d))
              (sourceTreeSeparatedMinorSum
                (blockCount n d) (blockWidth d) (blockColumns n d) d tree) := by
  let b := blockCount n d
  let t := blockWidth d
  let s := blockColumns n d
  have hrows : blockRows n d = b * t := rfl
  have hvariables : blockVariables n d = (b * t) * s := rfl
  have hdt : d ≤ t := by
    dsimp [t]
    unfold blockWidth
    omega
  let U : Matrix (Fin (b * t)) (Fin (b * t - d)) ℂ :=
    sourceTreeMatrix b t d hdt ζ tree hnodup hleaves
  let er : Fin n ≃ Fin (b * t) ⊕ Fin (s - d) :=
    sourceBlockRowEquiv hd hn
  let ec : Fin n ≃ Fin s ⊕ Fin (b * t - d) :=
    sourceBlockColumnEquiv hd hn
  let sub : Fin n × Fin n → FreeAffineInput (Fin (blockVariables n d)) :=
    fun ij => sourceBlockAffineInput U (er ij.1) (ec ij.2)
  refine ⟨sub, sourceTreeBlockCommonFactor b t s d,
    sourceTreeBlockCommonFactor_ne_zero b t s d, ?_⟩
  change
    MvPolynomial.aeval
        (fun ij : Fin n × Fin n =>
          (sourceBlockAffineInput U (er ij.1) (ec ij.2)).polynomial)
        (permanent n) =
      (MvPolynomial.C (sourceTreeBlockCommonFactor b t s d) :
        MvPolynomial (Fin ((b * t) * s)) ℂ) *
        MvPolynomial.rename
          (finProdFinEquiv : Fin (b * t) × Fin s ≃ Fin ((b * t) * s))
          (sourceTreeSeparatedMinorSum b t s d tree)
  rw [sourceBlock_affine_permanent_specialization er ec U,
    sourceBlockMatrix_rectangularPermanent_flatten]
  rw [sourceTreeBlockMatrix_permanent_eq_separated_minorSum
    b t s d (by omega) hdt hζ tree hnodup hleaves]
  simp [sourceTreeBlockCommonFactor, sourceTreeSeparatedMinorSum, map_mul]
end PermanentRollout
